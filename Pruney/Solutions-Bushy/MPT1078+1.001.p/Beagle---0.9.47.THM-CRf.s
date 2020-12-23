%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1078+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:22 EST 2020

% Result     : Theorem 15.71s
% Output     : CNFRefutation 16.04s
% Verified   : 
% Statistics : Number of formulae       :  141 (1979 expanded)
%              Number of leaves         :   39 ( 745 expanded)
%              Depth                    :   25
%              Number of atoms          :  464 (8988 expanded)
%              Number of equality atoms :   24 ( 440 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k2_partfun1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_170,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C,D,E,F] :
                ( ( v1_funct_1(F)
                  & v1_funct_2(F,A,B)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [G] :
                    ( ( v1_funct_1(G)
                      & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
                   => ( ( r1_tarski(k2_relset_1(A,B,F),k1_relset_1(B,C,k2_partfun1(B,C,G,D)))
                        & r1_tarski(D,E) )
                     => r2_funct_2(A,C,k8_funct_2(A,B,C,F,k2_partfun1(B,C,G,D)),k8_funct_2(A,B,C,F,k2_partfun1(B,C,G,E))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_36,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_52,axiom,(
    ! [A,B,C,D,E] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k8_funct_2(A,B,C,D,E))
        & v1_funct_2(k8_funct_2(A,B,C,D,E),A,C)
        & m1_subset_1(k8_funct_2(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k7_relat_1(C,A),k7_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_144,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_127,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C,D,E] :
              ( ( v1_funct_1(E)
                & v1_funct_2(E,A,B)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [F] :
                  ( ( v1_funct_1(F)
                    & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
                 => ( r1_tarski(k2_relset_1(A,B,E),k1_relset_1(B,C,k2_partfun1(B,C,F,D)))
                   => r2_funct_2(A,C,k8_funct_2(A,B,C,E,k2_partfun1(B,C,F,D)),k8_funct_2(A,B,C,E,F)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
       => r2_funct_2(A,B,D,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r2_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_44,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_178,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k2_partfun1(A_118,B_119,C_120,D_121) = k7_relat_1(C_120,D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_182,plain,(
    ! [D_121] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_7',D_121) = k7_relat_1('#skF_7',D_121)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_178])).

tff(c_188,plain,(
    ! [D_121] : k2_partfun1('#skF_2','#skF_3','#skF_7',D_121) = k7_relat_1('#skF_7',D_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_182])).

tff(c_148,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( v1_funct_1(k2_partfun1(A_105,B_106,C_107,D_108))
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ v1_funct_1(C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_152,plain,(
    ! [D_108] :
      ( v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_7',D_108))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_148])).

tff(c_158,plain,(
    ! [D_108] : v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_7',D_108)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_152])).

tff(c_202,plain,(
    ! [D_108] : v1_funct_1(k7_relat_1('#skF_7',D_108)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_158])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] :
      ( m1_subset_1(k2_partfun1(A_4,B_5,C_6,D_7),k1_zfmisc_1(k2_zfmisc_1(A_4,B_5)))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_471,plain,(
    ! [B_166,E_165,D_168,C_167,A_164] :
      ( v1_funct_2(k8_funct_2(A_164,B_166,C_167,D_168,E_165),A_164,C_167)
      | ~ m1_subset_1(E_165,k1_zfmisc_1(k2_zfmisc_1(B_166,C_167)))
      | ~ v1_funct_1(E_165)
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k2_zfmisc_1(A_164,B_166)))
      | ~ v1_funct_2(D_168,A_164,B_166)
      | ~ v1_funct_1(D_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2722,plain,(
    ! [A_528,D_532,A_533,B_529,C_530,D_531] :
      ( v1_funct_2(k8_funct_2(A_528,A_533,B_529,D_531,k2_partfun1(A_533,B_529,C_530,D_532)),A_528,B_529)
      | ~ v1_funct_1(k2_partfun1(A_533,B_529,C_530,D_532))
      | ~ m1_subset_1(D_531,k1_zfmisc_1(k2_zfmisc_1(A_528,A_533)))
      | ~ v1_funct_2(D_531,A_528,A_533)
      | ~ v1_funct_1(D_531)
      | ~ m1_subset_1(C_530,k1_zfmisc_1(k2_zfmisc_1(A_533,B_529)))
      | ~ v1_funct_1(C_530) ) ),
    inference(resolution,[status(thm)],[c_4,c_471])).

tff(c_2743,plain,(
    ! [A_528,D_531,D_121] :
      ( v1_funct_2(k8_funct_2(A_528,'#skF_2','#skF_3',D_531,k7_relat_1('#skF_7',D_121)),A_528,'#skF_3')
      | ~ v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_7',D_121))
      | ~ m1_subset_1(D_531,k1_zfmisc_1(k2_zfmisc_1(A_528,'#skF_2')))
      | ~ v1_funct_2(D_531,A_528,'#skF_2')
      | ~ v1_funct_1(D_531)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_2722])).

tff(c_2760,plain,(
    ! [A_528,D_531,D_121] :
      ( v1_funct_2(k8_funct_2(A_528,'#skF_2','#skF_3',D_531,k7_relat_1('#skF_7',D_121)),A_528,'#skF_3')
      | ~ m1_subset_1(D_531,k1_zfmisc_1(k2_zfmisc_1(A_528,'#skF_2')))
      | ~ v1_funct_2(D_531,A_528,'#skF_2')
      | ~ v1_funct_1(D_531) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_202,c_188,c_2743])).

tff(c_55,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_63,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_55])).

tff(c_38,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_26,plain,(
    ! [C_33,A_31,B_32] :
      ( r1_tarski(k7_relat_1(C_33,A_31),k7_relat_1(C_33,B_32))
      | ~ r1_tarski(A_31,B_32)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_270,plain,(
    ! [A_136,B_137,C_138,D_139] :
      ( m1_subset_1(k2_partfun1(A_136,B_137,C_138,D_139),k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ v1_funct_1(C_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_288,plain,(
    ! [D_121] :
      ( m1_subset_1(k7_relat_1('#skF_7',D_121),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_270])).

tff(c_302,plain,(
    ! [D_140] : m1_subset_1(k7_relat_1('#skF_7',D_140),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_288])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_329,plain,(
    ! [D_140] : v1_relat_1(k7_relat_1('#skF_7',D_140)) ),
    inference(resolution,[status(thm)],[c_302,c_2])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] :
      ( k1_relset_1(A_13,B_14,C_15) = k1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_328,plain,(
    ! [D_140] : k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_7',D_140)) = k1_relat_1(k7_relat_1('#skF_7',D_140)) ),
    inference(resolution,[status(thm)],[c_302,c_14])).

tff(c_103,plain,(
    ! [A_95,B_96,C_97] :
      ( k2_relset_1(A_95,B_96,C_97) = k2_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_110,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_103])).

tff(c_40,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_6'),k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_7','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_112,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_7','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_40])).

tff(c_203,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_7','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_112])).

tff(c_406,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relat_1(k7_relat_1('#skF_7','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_203])).

tff(c_141,plain,(
    ! [A_103,B_104] :
      ( r1_tarski(k1_relat_1(A_103),k1_relat_1(B_104))
      | ~ r1_tarski(A_103,B_104)
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_30,plain,(
    ! [A_57,C_59,B_58] :
      ( r1_tarski(A_57,C_59)
      | ~ r1_tarski(B_58,C_59)
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_147,plain,(
    ! [A_57,B_104,A_103] :
      ( r1_tarski(A_57,k1_relat_1(B_104))
      | ~ r1_tarski(A_57,k1_relat_1(A_103))
      | ~ r1_tarski(A_103,B_104)
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(A_103) ) ),
    inference(resolution,[status(thm)],[c_141,c_30])).

tff(c_418,plain,(
    ! [B_104] :
      ( r1_tarski(k2_relat_1('#skF_6'),k1_relat_1(B_104))
      | ~ r1_tarski(k7_relat_1('#skF_7','#skF_4'),B_104)
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_406,c_147])).

tff(c_425,plain,(
    ! [B_104] :
      ( r1_tarski(k2_relat_1('#skF_6'),k1_relat_1(B_104))
      | ~ r1_tarski(k7_relat_1('#skF_7','#skF_4'),B_104)
      | ~ v1_relat_1(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_418])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_299,plain,(
    ! [D_121] : m1_subset_1(k7_relat_1('#skF_7',D_121),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_288])).

tff(c_380,plain,(
    ! [E_151,B_152,A_150,C_153,D_154] :
      ( v1_funct_1(k8_funct_2(A_150,B_152,C_153,D_154,E_151))
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(B_152,C_153)))
      | ~ v1_funct_1(E_151)
      | ~ m1_subset_1(D_154,k1_zfmisc_1(k2_zfmisc_1(A_150,B_152)))
      | ~ v1_funct_2(D_154,A_150,B_152)
      | ~ v1_funct_1(D_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_384,plain,(
    ! [A_150,D_154,D_121] :
      ( v1_funct_1(k8_funct_2(A_150,'#skF_2','#skF_3',D_154,k7_relat_1('#skF_7',D_121)))
      | ~ v1_funct_1(k7_relat_1('#skF_7',D_121))
      | ~ m1_subset_1(D_154,k1_zfmisc_1(k2_zfmisc_1(A_150,'#skF_2')))
      | ~ v1_funct_2(D_154,A_150,'#skF_2')
      | ~ v1_funct_1(D_154) ) ),
    inference(resolution,[status(thm)],[c_299,c_380])).

tff(c_3171,plain,(
    ! [A_593,D_594,D_595] :
      ( v1_funct_1(k8_funct_2(A_593,'#skF_2','#skF_3',D_594,k7_relat_1('#skF_7',D_595)))
      | ~ m1_subset_1(D_594,k1_zfmisc_1(k2_zfmisc_1(A_593,'#skF_2')))
      | ~ v1_funct_2(D_594,A_593,'#skF_2')
      | ~ v1_funct_1(D_594) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_384])).

tff(c_3187,plain,(
    ! [D_595] :
      ( v1_funct_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7',D_595)))
      | ~ v1_funct_2('#skF_6','#skF_1','#skF_2')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_3171])).

tff(c_3204,plain,(
    ! [D_595] : v1_funct_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7',D_595))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3187])).

tff(c_390,plain,(
    ! [A_150,D_154] :
      ( v1_funct_1(k8_funct_2(A_150,'#skF_2','#skF_3',D_154,'#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_154,k1_zfmisc_1(k2_zfmisc_1(A_150,'#skF_2')))
      | ~ v1_funct_2(D_154,A_150,'#skF_2')
      | ~ v1_funct_1(D_154) ) ),
    inference(resolution,[status(thm)],[c_42,c_380])).

tff(c_535,plain,(
    ! [A_176,D_177] :
      ( v1_funct_1(k8_funct_2(A_176,'#skF_2','#skF_3',D_177,'#skF_7'))
      | ~ m1_subset_1(D_177,k1_zfmisc_1(k2_zfmisc_1(A_176,'#skF_2')))
      | ~ v1_funct_2(D_177,A_176,'#skF_2')
      | ~ v1_funct_1(D_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_390])).

tff(c_548,plain,
    ( v1_funct_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'))
    | ~ v1_funct_2('#skF_6','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_535])).

tff(c_558,plain,(
    v1_funct_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_548])).

tff(c_481,plain,(
    ! [A_164,D_168] :
      ( v1_funct_2(k8_funct_2(A_164,'#skF_2','#skF_3',D_168,'#skF_7'),A_164,'#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k2_zfmisc_1(A_164,'#skF_2')))
      | ~ v1_funct_2(D_168,A_164,'#skF_2')
      | ~ v1_funct_1(D_168) ) ),
    inference(resolution,[status(thm)],[c_42,c_471])).

tff(c_659,plain,(
    ! [A_196,D_197] :
      ( v1_funct_2(k8_funct_2(A_196,'#skF_2','#skF_3',D_197,'#skF_7'),A_196,'#skF_3')
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(A_196,'#skF_2')))
      | ~ v1_funct_2(D_197,A_196,'#skF_2')
      | ~ v1_funct_1(D_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_481])).

tff(c_668,plain,
    ( v1_funct_2(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),'#skF_1','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_659])).

tff(c_678,plain,(
    v1_funct_2(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),'#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_668])).

tff(c_8,plain,(
    ! [E_12,D_11,A_8,C_10,B_9] :
      ( m1_subset_1(k8_funct_2(A_8,B_9,C_10,D_11,E_12),k1_zfmisc_1(k2_zfmisc_1(A_8,C_10)))
      | ~ m1_subset_1(E_12,k1_zfmisc_1(k2_zfmisc_1(B_9,C_10)))
      | ~ v1_funct_1(E_12)
      | ~ m1_subset_1(D_11,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(D_11,A_8,B_9)
      | ~ v1_funct_1(D_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_715,plain,(
    ! [C_211,B_210,D_212,E_209,A_208] :
      ( m1_subset_1(k8_funct_2(A_208,B_210,C_211,D_212,E_209),k1_zfmisc_1(k2_zfmisc_1(A_208,C_211)))
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(B_210,C_211)))
      | ~ v1_funct_1(E_209)
      | ~ m1_subset_1(D_212,k1_zfmisc_1(k2_zfmisc_1(A_208,B_210)))
      | ~ v1_funct_2(D_212,A_208,B_210)
      | ~ v1_funct_1(D_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_16,B_17,C_18,D_19] :
      ( k2_partfun1(A_16,B_17,C_18,D_19) = k7_relat_1(C_18,D_19)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ v1_funct_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2878,plain,(
    ! [B_565,D_563,C_567,A_564,D_566,E_562] :
      ( k2_partfun1(A_564,C_567,k8_funct_2(A_564,B_565,C_567,D_563,E_562),D_566) = k7_relat_1(k8_funct_2(A_564,B_565,C_567,D_563,E_562),D_566)
      | ~ v1_funct_1(k8_funct_2(A_564,B_565,C_567,D_563,E_562))
      | ~ m1_subset_1(E_562,k1_zfmisc_1(k2_zfmisc_1(B_565,C_567)))
      | ~ v1_funct_1(E_562)
      | ~ m1_subset_1(D_563,k1_zfmisc_1(k2_zfmisc_1(A_564,B_565)))
      | ~ v1_funct_2(D_563,A_564,B_565)
      | ~ v1_funct_1(D_563) ) ),
    inference(resolution,[status(thm)],[c_715,c_16])).

tff(c_2884,plain,(
    ! [D_566] :
      ( k2_partfun1('#skF_1','#skF_3',k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),D_566) = k7_relat_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),D_566)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_2('#skF_6','#skF_1','#skF_2')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_558,c_2878])).

tff(c_2893,plain,(
    ! [D_566] : k2_partfun1('#skF_1','#skF_3',k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),D_566) = k7_relat_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),D_566) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_2884])).

tff(c_2894,plain,(
    ! [D_568] : k2_partfun1('#skF_1','#skF_3',k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),D_568) = k7_relat_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),D_568) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_2884])).

tff(c_28,plain,(
    ! [E_54,F_56,A_34,C_52,D_53,B_46] :
      ( r2_funct_2(A_34,C_52,k8_funct_2(A_34,B_46,C_52,E_54,k2_partfun1(B_46,C_52,F_56,D_53)),k8_funct_2(A_34,B_46,C_52,E_54,F_56))
      | ~ r1_tarski(k2_relset_1(A_34,B_46,E_54),k1_relset_1(B_46,C_52,k2_partfun1(B_46,C_52,F_56,D_53)))
      | ~ m1_subset_1(F_56,k1_zfmisc_1(k2_zfmisc_1(B_46,C_52)))
      | ~ v1_funct_1(F_56)
      | ~ m1_subset_1(E_54,k1_zfmisc_1(k2_zfmisc_1(A_34,B_46)))
      | ~ v1_funct_2(E_54,A_34,B_46)
      | ~ v1_funct_1(E_54)
      | v1_xboole_0(B_46)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2911,plain,(
    ! [A_34,E_54,D_568] :
      ( r2_funct_2(A_34,'#skF_3',k8_funct_2(A_34,'#skF_1','#skF_3',E_54,k7_relat_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),D_568)),k8_funct_2(A_34,'#skF_1','#skF_3',E_54,k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7')))
      | ~ r1_tarski(k2_relset_1(A_34,'#skF_1',E_54),k1_relset_1('#skF_1','#skF_3',k2_partfun1('#skF_1','#skF_3',k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),D_568)))
      | ~ m1_subset_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'))
      | ~ m1_subset_1(E_54,k1_zfmisc_1(k2_zfmisc_1(A_34,'#skF_1')))
      | ~ v1_funct_2(E_54,A_34,'#skF_1')
      | ~ v1_funct_1(E_54)
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2894,c_28])).

tff(c_2928,plain,(
    ! [A_34,E_54,D_568] :
      ( r2_funct_2(A_34,'#skF_3',k8_funct_2(A_34,'#skF_1','#skF_3',E_54,k7_relat_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),D_568)),k8_funct_2(A_34,'#skF_1','#skF_3',E_54,k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7')))
      | ~ r1_tarski(k2_relset_1(A_34,'#skF_1',E_54),k1_relset_1('#skF_1','#skF_3',k7_relat_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),D_568)))
      | ~ m1_subset_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ m1_subset_1(E_54,k1_zfmisc_1(k2_zfmisc_1(A_34,'#skF_1')))
      | ~ v1_funct_2(E_54,A_34,'#skF_1')
      | ~ v1_funct_1(E_54)
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_2893,c_2911])).

tff(c_2929,plain,(
    ! [A_34,E_54,D_568] :
      ( r2_funct_2(A_34,'#skF_3',k8_funct_2(A_34,'#skF_1','#skF_3',E_54,k7_relat_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),D_568)),k8_funct_2(A_34,'#skF_1','#skF_3',E_54,k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7')))
      | ~ r1_tarski(k2_relset_1(A_34,'#skF_1',E_54),k1_relset_1('#skF_1','#skF_3',k7_relat_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),D_568)))
      | ~ m1_subset_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ m1_subset_1(E_54,k1_zfmisc_1(k2_zfmisc_1(A_34,'#skF_1')))
      | ~ v1_funct_2(E_54,A_34,'#skF_1')
      | ~ v1_funct_1(E_54)
      | v1_xboole_0(A_34) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2928])).

tff(c_2935,plain,(
    ~ m1_subset_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2929])).

tff(c_2947,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_6','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_2935])).

tff(c_2951,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_2947])).

tff(c_2953,plain,(
    m1_subset_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2929])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_929,plain,(
    ! [A_252,E_251,D_256,B_253,C_254,F_255] :
      ( r2_funct_2(A_252,C_254,k8_funct_2(A_252,B_253,C_254,E_251,k2_partfun1(B_253,C_254,F_255,D_256)),k8_funct_2(A_252,B_253,C_254,E_251,F_255))
      | ~ r1_tarski(k2_relset_1(A_252,B_253,E_251),k1_relset_1(B_253,C_254,k2_partfun1(B_253,C_254,F_255,D_256)))
      | ~ m1_subset_1(F_255,k1_zfmisc_1(k2_zfmisc_1(B_253,C_254)))
      | ~ v1_funct_1(F_255)
      | ~ m1_subset_1(E_251,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253)))
      | ~ v1_funct_2(E_251,A_252,B_253)
      | ~ v1_funct_1(E_251)
      | v1_xboole_0(B_253)
      | v1_xboole_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_24,plain,(
    ! [A_27,B_28,D_30,C_29] :
      ( r2_funct_2(A_27,B_28,D_30,C_29)
      | ~ r2_funct_2(A_27,B_28,C_29,D_30)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(D_30,A_27,B_28)
      | ~ v1_funct_1(D_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(C_29,A_27,B_28)
      | ~ v1_funct_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3876,plain,(
    ! [B_681,A_680,E_677,F_678,D_679,C_676] :
      ( r2_funct_2(A_680,C_676,k8_funct_2(A_680,B_681,C_676,E_677,F_678),k8_funct_2(A_680,B_681,C_676,E_677,k2_partfun1(B_681,C_676,F_678,D_679)))
      | ~ m1_subset_1(k8_funct_2(A_680,B_681,C_676,E_677,F_678),k1_zfmisc_1(k2_zfmisc_1(A_680,C_676)))
      | ~ v1_funct_2(k8_funct_2(A_680,B_681,C_676,E_677,F_678),A_680,C_676)
      | ~ v1_funct_1(k8_funct_2(A_680,B_681,C_676,E_677,F_678))
      | ~ m1_subset_1(k8_funct_2(A_680,B_681,C_676,E_677,k2_partfun1(B_681,C_676,F_678,D_679)),k1_zfmisc_1(k2_zfmisc_1(A_680,C_676)))
      | ~ v1_funct_2(k8_funct_2(A_680,B_681,C_676,E_677,k2_partfun1(B_681,C_676,F_678,D_679)),A_680,C_676)
      | ~ v1_funct_1(k8_funct_2(A_680,B_681,C_676,E_677,k2_partfun1(B_681,C_676,F_678,D_679)))
      | ~ r1_tarski(k2_relset_1(A_680,B_681,E_677),k1_relset_1(B_681,C_676,k2_partfun1(B_681,C_676,F_678,D_679)))
      | ~ m1_subset_1(F_678,k1_zfmisc_1(k2_zfmisc_1(B_681,C_676)))
      | ~ v1_funct_1(F_678)
      | ~ m1_subset_1(E_677,k1_zfmisc_1(k2_zfmisc_1(A_680,B_681)))
      | ~ v1_funct_2(E_677,A_680,B_681)
      | ~ v1_funct_1(E_677)
      | v1_xboole_0(B_681)
      | v1_xboole_0(A_680) ) ),
    inference(resolution,[status(thm)],[c_929,c_24])).

tff(c_13574,plain,(
    ! [D_1955,D_1951,B_1953,C_1954,F_1950,A_1952] :
      ( r2_funct_2(A_1952,C_1954,k8_funct_2(A_1952,B_1953,C_1954,D_1955,F_1950),k8_funct_2(A_1952,B_1953,C_1954,D_1955,k2_partfun1(B_1953,C_1954,F_1950,D_1951)))
      | ~ m1_subset_1(k8_funct_2(A_1952,B_1953,C_1954,D_1955,F_1950),k1_zfmisc_1(k2_zfmisc_1(A_1952,C_1954)))
      | ~ v1_funct_2(k8_funct_2(A_1952,B_1953,C_1954,D_1955,F_1950),A_1952,C_1954)
      | ~ v1_funct_1(k8_funct_2(A_1952,B_1953,C_1954,D_1955,F_1950))
      | ~ v1_funct_2(k8_funct_2(A_1952,B_1953,C_1954,D_1955,k2_partfun1(B_1953,C_1954,F_1950,D_1951)),A_1952,C_1954)
      | ~ v1_funct_1(k8_funct_2(A_1952,B_1953,C_1954,D_1955,k2_partfun1(B_1953,C_1954,F_1950,D_1951)))
      | ~ r1_tarski(k2_relset_1(A_1952,B_1953,D_1955),k1_relset_1(B_1953,C_1954,k2_partfun1(B_1953,C_1954,F_1950,D_1951)))
      | ~ m1_subset_1(F_1950,k1_zfmisc_1(k2_zfmisc_1(B_1953,C_1954)))
      | ~ v1_funct_1(F_1950)
      | v1_xboole_0(B_1953)
      | v1_xboole_0(A_1952)
      | ~ m1_subset_1(k2_partfun1(B_1953,C_1954,F_1950,D_1951),k1_zfmisc_1(k2_zfmisc_1(B_1953,C_1954)))
      | ~ v1_funct_1(k2_partfun1(B_1953,C_1954,F_1950,D_1951))
      | ~ m1_subset_1(D_1955,k1_zfmisc_1(k2_zfmisc_1(A_1952,B_1953)))
      | ~ v1_funct_2(D_1955,A_1952,B_1953)
      | ~ v1_funct_1(D_1955) ) ),
    inference(resolution,[status(thm)],[c_8,c_3876])).

tff(c_13623,plain,(
    ! [A_1952,D_1955,D_121] :
      ( r2_funct_2(A_1952,'#skF_3',k8_funct_2(A_1952,'#skF_2','#skF_3',D_1955,'#skF_7'),k8_funct_2(A_1952,'#skF_2','#skF_3',D_1955,k7_relat_1('#skF_7',D_121)))
      | ~ m1_subset_1(k8_funct_2(A_1952,'#skF_2','#skF_3',D_1955,'#skF_7'),k1_zfmisc_1(k2_zfmisc_1(A_1952,'#skF_3')))
      | ~ v1_funct_2(k8_funct_2(A_1952,'#skF_2','#skF_3',D_1955,'#skF_7'),A_1952,'#skF_3')
      | ~ v1_funct_1(k8_funct_2(A_1952,'#skF_2','#skF_3',D_1955,'#skF_7'))
      | ~ v1_funct_2(k8_funct_2(A_1952,'#skF_2','#skF_3',D_1955,k2_partfun1('#skF_2','#skF_3','#skF_7',D_121)),A_1952,'#skF_3')
      | ~ v1_funct_1(k8_funct_2(A_1952,'#skF_2','#skF_3',D_1955,k2_partfun1('#skF_2','#skF_3','#skF_7',D_121)))
      | ~ r1_tarski(k2_relset_1(A_1952,'#skF_2',D_1955),k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_7',D_121)))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1952)
      | ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_7',D_121),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_7',D_121))
      | ~ m1_subset_1(D_1955,k1_zfmisc_1(k2_zfmisc_1(A_1952,'#skF_2')))
      | ~ v1_funct_2(D_1955,A_1952,'#skF_2')
      | ~ v1_funct_1(D_1955) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_13574])).

tff(c_13672,plain,(
    ! [A_1952,D_1955,D_121] :
      ( r2_funct_2(A_1952,'#skF_3',k8_funct_2(A_1952,'#skF_2','#skF_3',D_1955,'#skF_7'),k8_funct_2(A_1952,'#skF_2','#skF_3',D_1955,k7_relat_1('#skF_7',D_121)))
      | ~ m1_subset_1(k8_funct_2(A_1952,'#skF_2','#skF_3',D_1955,'#skF_7'),k1_zfmisc_1(k2_zfmisc_1(A_1952,'#skF_3')))
      | ~ v1_funct_2(k8_funct_2(A_1952,'#skF_2','#skF_3',D_1955,'#skF_7'),A_1952,'#skF_3')
      | ~ v1_funct_1(k8_funct_2(A_1952,'#skF_2','#skF_3',D_1955,'#skF_7'))
      | ~ v1_funct_2(k8_funct_2(A_1952,'#skF_2','#skF_3',D_1955,k7_relat_1('#skF_7',D_121)),A_1952,'#skF_3')
      | ~ v1_funct_1(k8_funct_2(A_1952,'#skF_2','#skF_3',D_1955,k7_relat_1('#skF_7',D_121)))
      | ~ r1_tarski(k2_relset_1(A_1952,'#skF_2',D_1955),k1_relat_1(k7_relat_1('#skF_7',D_121)))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1952)
      | ~ m1_subset_1(D_1955,k1_zfmisc_1(k2_zfmisc_1(A_1952,'#skF_2')))
      | ~ v1_funct_2(D_1955,A_1952,'#skF_2')
      | ~ v1_funct_1(D_1955) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_188,c_299,c_188,c_44,c_42,c_328,c_188,c_188,c_188,c_13623])).

tff(c_15164,plain,(
    ! [A_2094,D_2095,D_2096] :
      ( r2_funct_2(A_2094,'#skF_3',k8_funct_2(A_2094,'#skF_2','#skF_3',D_2095,'#skF_7'),k8_funct_2(A_2094,'#skF_2','#skF_3',D_2095,k7_relat_1('#skF_7',D_2096)))
      | ~ m1_subset_1(k8_funct_2(A_2094,'#skF_2','#skF_3',D_2095,'#skF_7'),k1_zfmisc_1(k2_zfmisc_1(A_2094,'#skF_3')))
      | ~ v1_funct_2(k8_funct_2(A_2094,'#skF_2','#skF_3',D_2095,'#skF_7'),A_2094,'#skF_3')
      | ~ v1_funct_1(k8_funct_2(A_2094,'#skF_2','#skF_3',D_2095,'#skF_7'))
      | ~ v1_funct_2(k8_funct_2(A_2094,'#skF_2','#skF_3',D_2095,k7_relat_1('#skF_7',D_2096)),A_2094,'#skF_3')
      | ~ v1_funct_1(k8_funct_2(A_2094,'#skF_2','#skF_3',D_2095,k7_relat_1('#skF_7',D_2096)))
      | ~ r1_tarski(k2_relset_1(A_2094,'#skF_2',D_2095),k1_relat_1(k7_relat_1('#skF_7',D_2096)))
      | v1_xboole_0(A_2094)
      | ~ m1_subset_1(D_2095,k1_zfmisc_1(k2_zfmisc_1(A_2094,'#skF_2')))
      | ~ v1_funct_2(D_2095,A_2094,'#skF_2')
      | ~ v1_funct_1(D_2095) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_13672])).

tff(c_22,plain,(
    ! [D_26,C_25,A_23,B_24] :
      ( D_26 = C_25
      | ~ r2_funct_2(A_23,B_24,C_25,D_26)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_funct_2(D_26,A_23,B_24)
      | ~ v1_funct_1(D_26)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_funct_2(C_25,A_23,B_24)
      | ~ v1_funct_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3518,plain,(
    ! [B_649,C_644,A_648,E_645,D_647,F_646] :
      ( k8_funct_2(A_648,B_649,C_644,E_645,k2_partfun1(B_649,C_644,F_646,D_647)) = k8_funct_2(A_648,B_649,C_644,E_645,F_646)
      | ~ m1_subset_1(k8_funct_2(A_648,B_649,C_644,E_645,F_646),k1_zfmisc_1(k2_zfmisc_1(A_648,C_644)))
      | ~ v1_funct_2(k8_funct_2(A_648,B_649,C_644,E_645,F_646),A_648,C_644)
      | ~ v1_funct_1(k8_funct_2(A_648,B_649,C_644,E_645,F_646))
      | ~ m1_subset_1(k8_funct_2(A_648,B_649,C_644,E_645,k2_partfun1(B_649,C_644,F_646,D_647)),k1_zfmisc_1(k2_zfmisc_1(A_648,C_644)))
      | ~ v1_funct_2(k8_funct_2(A_648,B_649,C_644,E_645,k2_partfun1(B_649,C_644,F_646,D_647)),A_648,C_644)
      | ~ v1_funct_1(k8_funct_2(A_648,B_649,C_644,E_645,k2_partfun1(B_649,C_644,F_646,D_647)))
      | ~ r1_tarski(k2_relset_1(A_648,B_649,E_645),k1_relset_1(B_649,C_644,k2_partfun1(B_649,C_644,F_646,D_647)))
      | ~ m1_subset_1(F_646,k1_zfmisc_1(k2_zfmisc_1(B_649,C_644)))
      | ~ v1_funct_1(F_646)
      | ~ m1_subset_1(E_645,k1_zfmisc_1(k2_zfmisc_1(A_648,B_649)))
      | ~ v1_funct_2(E_645,A_648,B_649)
      | ~ v1_funct_1(E_645)
      | v1_xboole_0(B_649)
      | v1_xboole_0(A_648) ) ),
    inference(resolution,[status(thm)],[c_929,c_22])).

tff(c_13258,plain,(
    ! [D_1936,D_1935,C_1934,F_1931,B_1933,A_1932] :
      ( k8_funct_2(A_1932,B_1933,C_1934,D_1936,k2_partfun1(B_1933,C_1934,F_1931,D_1935)) = k8_funct_2(A_1932,B_1933,C_1934,D_1936,F_1931)
      | ~ m1_subset_1(k8_funct_2(A_1932,B_1933,C_1934,D_1936,F_1931),k1_zfmisc_1(k2_zfmisc_1(A_1932,C_1934)))
      | ~ v1_funct_2(k8_funct_2(A_1932,B_1933,C_1934,D_1936,F_1931),A_1932,C_1934)
      | ~ v1_funct_1(k8_funct_2(A_1932,B_1933,C_1934,D_1936,F_1931))
      | ~ v1_funct_2(k8_funct_2(A_1932,B_1933,C_1934,D_1936,k2_partfun1(B_1933,C_1934,F_1931,D_1935)),A_1932,C_1934)
      | ~ v1_funct_1(k8_funct_2(A_1932,B_1933,C_1934,D_1936,k2_partfun1(B_1933,C_1934,F_1931,D_1935)))
      | ~ r1_tarski(k2_relset_1(A_1932,B_1933,D_1936),k1_relset_1(B_1933,C_1934,k2_partfun1(B_1933,C_1934,F_1931,D_1935)))
      | ~ m1_subset_1(F_1931,k1_zfmisc_1(k2_zfmisc_1(B_1933,C_1934)))
      | ~ v1_funct_1(F_1931)
      | v1_xboole_0(B_1933)
      | v1_xboole_0(A_1932)
      | ~ m1_subset_1(k2_partfun1(B_1933,C_1934,F_1931,D_1935),k1_zfmisc_1(k2_zfmisc_1(B_1933,C_1934)))
      | ~ v1_funct_1(k2_partfun1(B_1933,C_1934,F_1931,D_1935))
      | ~ m1_subset_1(D_1936,k1_zfmisc_1(k2_zfmisc_1(A_1932,B_1933)))
      | ~ v1_funct_2(D_1936,A_1932,B_1933)
      | ~ v1_funct_1(D_1936) ) ),
    inference(resolution,[status(thm)],[c_8,c_3518])).

tff(c_13260,plain,(
    ! [D_1935] :
      ( k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k2_partfun1('#skF_2','#skF_3','#skF_7',D_1935)) = k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7')
      | ~ v1_funct_2(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),'#skF_1','#skF_3')
      | ~ v1_funct_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'))
      | ~ v1_funct_2(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k2_partfun1('#skF_2','#skF_3','#skF_7',D_1935)),'#skF_1','#skF_3')
      | ~ v1_funct_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k2_partfun1('#skF_2','#skF_3','#skF_7',D_1935)))
      | ~ r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_6'),k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_7',D_1935)))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | v1_xboole_0('#skF_2')
      | v1_xboole_0('#skF_1')
      | ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_7',D_1935),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_7',D_1935))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_2('#skF_6','#skF_1','#skF_2')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2953,c_13258])).

tff(c_13265,plain,(
    ! [D_1935] :
      ( k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7',D_1935)) = k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7')
      | ~ v1_funct_2(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7',D_1935)),'#skF_1','#skF_3')
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1(k7_relat_1('#skF_7',D_1935)))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_202,c_188,c_299,c_188,c_44,c_42,c_110,c_328,c_188,c_3204,c_188,c_188,c_558,c_678,c_188,c_13260])).

tff(c_13388,plain,(
    ! [D_1949] :
      ( k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7',D_1949)) = k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7')
      | ~ v1_funct_2(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7',D_1949)),'#skF_1','#skF_3')
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1(k7_relat_1('#skF_7',D_1949))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_13265])).

tff(c_13417,plain,
    ( k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7','#skF_4')) = k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7')
    | ~ v1_funct_2(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7','#skF_4')),'#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_406,c_13388])).

tff(c_13418,plain,(
    ~ v1_funct_2(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7','#skF_4')),'#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_13417])).

tff(c_13421,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_6','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2760,c_13418])).

tff(c_13425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_13421])).

tff(c_13426,plain,(
    k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7','#skF_4')) = k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_13417])).

tff(c_36,plain,(
    ~ r2_funct_2('#skF_1','#skF_3',k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k2_partfun1('#skF_2','#skF_3','#skF_7','#skF_4')),k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k2_partfun1('#skF_2','#skF_3','#skF_7','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_204,plain,(
    ~ r2_funct_2('#skF_1','#skF_3',k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7','#skF_4')),k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_188,c_36])).

tff(c_13429,plain,(
    ~ r2_funct_2('#skF_1','#skF_3',k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13426,c_204])).

tff(c_15167,plain,
    ( ~ m1_subset_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'),'#skF_1','#skF_3')
    | ~ v1_funct_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6','#skF_7'))
    | ~ v1_funct_2(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7','#skF_5')),'#skF_1','#skF_3')
    | ~ v1_funct_1(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7','#skF_5')))
    | ~ r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_6'),k1_relat_1(k7_relat_1('#skF_7','#skF_5')))
    | v1_xboole_0('#skF_1')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_6','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_15164,c_13429])).

tff(c_15177,plain,
    ( ~ v1_funct_2(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7','#skF_5')),'#skF_1','#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1(k7_relat_1('#skF_7','#skF_5')))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_110,c_3204,c_558,c_678,c_2953,c_15167])).

tff(c_15178,plain,
    ( ~ v1_funct_2(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7','#skF_5')),'#skF_1','#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1(k7_relat_1('#skF_7','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_15177])).

tff(c_15184,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1(k7_relat_1('#skF_7','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_15178])).

tff(c_15193,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_7','#skF_4'),k7_relat_1('#skF_7','#skF_5'))
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_5')) ),
    inference(resolution,[status(thm)],[c_425,c_15184])).

tff(c_15200,plain,(
    ~ r1_tarski(k7_relat_1('#skF_7','#skF_4'),k7_relat_1('#skF_7','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_15193])).

tff(c_15215,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_15200])).

tff(c_15225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_38,c_15215])).

tff(c_15226,plain,(
    ~ v1_funct_2(k8_funct_2('#skF_1','#skF_2','#skF_3','#skF_6',k7_relat_1('#skF_7','#skF_5')),'#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_15178])).

tff(c_15670,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_6','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2760,c_15226])).

tff(c_15674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_15670])).

%------------------------------------------------------------------------------
