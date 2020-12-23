%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:14 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 198 expanded)
%              Number of leaves         :   35 (  86 expanded)
%              Depth                    :   15
%              Number of atoms          :  216 ( 726 expanded)
%              Number of equality atoms :   35 (  86 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C,D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                   => ! [F] :
                        ( m1_subset_1(F,B)
                       => ( v1_partfun1(E,A)
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k7_partfun1(C,E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_123,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C,D] :
              ( ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
             => ! [E] :
                  ( ( v1_funct_1(E)
                    & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                 => ! [F] :
                      ( m1_subset_1(F,B)
                     => ( v1_partfun1(E,A)
                       => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k1_funct_1(E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_30,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_55,plain,(
    ! [C_95,B_96,A_97] :
      ( v5_relat_1(C_95,B_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_62,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_55])).

tff(c_45,plain,(
    ! [C_90,A_91,B_92] :
      ( v1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_45])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_64,plain,(
    ! [C_98,A_99,B_100] :
      ( v4_relat_1(C_98,A_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_64])).

tff(c_74,plain,(
    ! [B_102,A_103] :
      ( k1_relat_1(B_102) = A_103
      | ~ v1_partfun1(B_102,A_103)
      | ~ v4_relat_1(B_102,A_103)
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_77,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_71,c_74])).

tff(c_83,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_77])).

tff(c_96,plain,(
    ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_38,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_124,plain,(
    ! [C_111,A_112,B_113] :
      ( v1_partfun1(C_111,A_112)
      | ~ v1_funct_2(C_111,A_112,B_113)
      | ~ v1_funct_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | v1_xboole_0(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_131,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_124])).

tff(c_138,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_131])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_96,c_138])).

tff(c_141,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_153,plain,(
    ! [C_114,B_115,A_116] :
      ( m1_subset_1(k1_funct_1(C_114,B_115),A_116)
      | ~ r2_hidden(B_115,k1_relat_1(C_114))
      | ~ v1_funct_1(C_114)
      | ~ v5_relat_1(C_114,A_116)
      | ~ v1_relat_1(C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_155,plain,(
    ! [B_115,A_116] :
      ( m1_subset_1(k1_funct_1('#skF_4',B_115),A_116)
      | ~ r2_hidden(B_115,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_116)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_153])).

tff(c_162,plain,(
    ! [B_115,A_116] :
      ( m1_subset_1(k1_funct_1('#skF_4',B_115),A_116)
      | ~ r2_hidden(B_115,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_40,c_155])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_63,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_55])).

tff(c_53,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_45])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_28,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_72,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_64])).

tff(c_80,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_74])).

tff(c_86,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_28,c_80])).

tff(c_226,plain,(
    ! [A_128,B_129,C_130] :
      ( k7_partfun1(A_128,B_129,C_130) = k1_funct_1(B_129,C_130)
      | ~ r2_hidden(C_130,k1_relat_1(B_129))
      | ~ v1_funct_1(B_129)
      | ~ v5_relat_1(B_129,A_128)
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_230,plain,(
    ! [A_128,C_130] :
      ( k7_partfun1(A_128,'#skF_5',C_130) = k1_funct_1('#skF_5',C_130)
      | ~ r2_hidden(C_130,'#skF_1')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_128)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_226])).

tff(c_269,plain,(
    ! [A_136,C_137] :
      ( k7_partfun1(A_136,'#skF_5',C_137) = k1_funct_1('#skF_5',C_137)
      | ~ r2_hidden(C_137,'#skF_1')
      | ~ v5_relat_1('#skF_5',A_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_34,c_230])).

tff(c_272,plain,(
    ! [A_136,A_1] :
      ( k7_partfun1(A_136,'#skF_5',A_1) = k1_funct_1('#skF_5',A_1)
      | ~ v5_relat_1('#skF_5',A_136)
      | v1_xboole_0('#skF_1')
      | ~ m1_subset_1(A_1,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2,c_269])).

tff(c_276,plain,(
    ! [A_138,A_139] :
      ( k7_partfun1(A_138,'#skF_5',A_139) = k1_funct_1('#skF_5',A_139)
      | ~ v5_relat_1('#skF_5',A_138)
      | ~ m1_subset_1(A_139,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_272])).

tff(c_280,plain,(
    ! [A_140] :
      ( k7_partfun1('#skF_3','#skF_5',A_140) = k1_funct_1('#skF_5',A_140)
      | ~ m1_subset_1(A_140,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_63,c_276])).

tff(c_288,plain,(
    ! [B_115] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_115)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_115))
      | ~ r2_hidden(B_115,'#skF_2')
      | ~ v5_relat_1('#skF_4','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_162,c_280])).

tff(c_292,plain,(
    ! [B_115] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_115)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_115))
      | ~ r2_hidden(B_115,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_288])).

tff(c_293,plain,(
    ! [A_141,B_142,C_143,D_144] :
      ( k3_funct_2(A_141,B_142,C_143,D_144) = k1_funct_1(C_143,D_144)
      | ~ m1_subset_1(D_144,A_141)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_2(C_143,A_141,B_142)
      | ~ v1_funct_1(C_143)
      | v1_xboole_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_303,plain,(
    ! [B_142,C_143] :
      ( k3_funct_2('#skF_2',B_142,C_143,'#skF_6') = k1_funct_1(C_143,'#skF_6')
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_142)))
      | ~ v1_funct_2(C_143,'#skF_2',B_142)
      | ~ v1_funct_1(C_143)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_293])).

tff(c_321,plain,(
    ! [B_146,C_147] :
      ( k3_funct_2('#skF_2',B_146,C_147,'#skF_6') = k1_funct_1(C_147,'#skF_6')
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_146)))
      | ~ v1_funct_2(C_147,'#skF_2',B_146)
      | ~ v1_funct_1(C_147) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_303])).

tff(c_332,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_321])).

tff(c_337,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_332])).

tff(c_345,plain,(
    ! [F_153,E_148,A_149,B_152,D_151,C_150] :
      ( k3_funct_2(B_152,C_150,k8_funct_2(B_152,A_149,C_150,D_151,E_148),F_153) = k1_funct_1(E_148,k3_funct_2(B_152,A_149,D_151,F_153))
      | ~ v1_partfun1(E_148,A_149)
      | ~ m1_subset_1(F_153,B_152)
      | ~ m1_subset_1(E_148,k1_zfmisc_1(k2_zfmisc_1(A_149,C_150)))
      | ~ v1_funct_1(E_148)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(B_152,A_149)))
      | ~ v1_funct_2(D_151,B_152,A_149)
      | ~ v1_funct_1(D_151)
      | v1_xboole_0(B_152)
      | v1_xboole_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_355,plain,(
    ! [B_152,D_151,F_153] :
      ( k3_funct_2(B_152,'#skF_3',k8_funct_2(B_152,'#skF_1','#skF_3',D_151,'#skF_5'),F_153) = k1_funct_1('#skF_5',k3_funct_2(B_152,'#skF_1',D_151,F_153))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_153,B_152)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(B_152,'#skF_1')))
      | ~ v1_funct_2(D_151,B_152,'#skF_1')
      | ~ v1_funct_1(D_151)
      | v1_xboole_0(B_152)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_345])).

tff(c_364,plain,(
    ! [B_152,D_151,F_153] :
      ( k3_funct_2(B_152,'#skF_3',k8_funct_2(B_152,'#skF_1','#skF_3',D_151,'#skF_5'),F_153) = k1_funct_1('#skF_5',k3_funct_2(B_152,'#skF_1',D_151,F_153))
      | ~ m1_subset_1(F_153,B_152)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(B_152,'#skF_1')))
      | ~ v1_funct_2(D_151,B_152,'#skF_1')
      | ~ v1_funct_1(D_151)
      | v1_xboole_0(B_152)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_355])).

tff(c_454,plain,(
    ! [B_174,D_175,F_176] :
      ( k3_funct_2(B_174,'#skF_3',k8_funct_2(B_174,'#skF_1','#skF_3',D_175,'#skF_5'),F_176) = k1_funct_1('#skF_5',k3_funct_2(B_174,'#skF_1',D_175,F_176))
      | ~ m1_subset_1(F_176,B_174)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(k2_zfmisc_1(B_174,'#skF_1')))
      | ~ v1_funct_2(D_175,B_174,'#skF_1')
      | ~ v1_funct_1(D_175)
      | v1_xboole_0(B_174) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_364])).

tff(c_465,plain,(
    ! [F_176] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_176) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_176))
      | ~ m1_subset_1(F_176,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_454])).

tff(c_471,plain,(
    ! [F_176] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_176) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_176))
      | ~ m1_subset_1(F_176,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_465])).

tff(c_473,plain,(
    ! [F_177] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_177) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_177))
      | ~ m1_subset_1(F_177,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_471])).

tff(c_26,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_338,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_26])).

tff(c_479,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_338])).

tff(c_485,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_337,c_479])).

tff(c_490,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_485])).

tff(c_493,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_490])).

tff(c_496,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_493])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_496])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:54:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.40  
% 2.81/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.40  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.81/1.40  
% 2.81/1.40  %Foreground sorts:
% 2.81/1.40  
% 2.81/1.40  
% 2.81/1.40  %Background operators:
% 2.81/1.40  
% 2.81/1.40  
% 2.81/1.40  %Foreground operators:
% 2.81/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.40  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.81/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.81/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.81/1.40  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.81/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.81/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.40  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.81/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.81/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.81/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.40  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.81/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.40  
% 2.81/1.42  tff(f_150, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_funct_2)).
% 2.81/1.42  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.81/1.42  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.81/1.42  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.81/1.42  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.81/1.42  tff(f_65, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.81/1.42  tff(f_41, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 2.81/1.42  tff(f_84, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 2.81/1.42  tff(f_97, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.81/1.42  tff(f_123, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 2.81/1.42  tff(c_42, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.81/1.42  tff(c_30, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.81/1.42  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.42  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.81/1.42  tff(c_55, plain, (![C_95, B_96, A_97]: (v5_relat_1(C_95, B_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.81/1.42  tff(c_62, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_55])).
% 2.81/1.42  tff(c_45, plain, (![C_90, A_91, B_92]: (v1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.42  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_45])).
% 2.81/1.42  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.81/1.42  tff(c_44, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.81/1.42  tff(c_64, plain, (![C_98, A_99, B_100]: (v4_relat_1(C_98, A_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.81/1.42  tff(c_71, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_64])).
% 2.81/1.42  tff(c_74, plain, (![B_102, A_103]: (k1_relat_1(B_102)=A_103 | ~v1_partfun1(B_102, A_103) | ~v4_relat_1(B_102, A_103) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.42  tff(c_77, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_71, c_74])).
% 2.81/1.42  tff(c_83, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_77])).
% 2.81/1.42  tff(c_96, plain, (~v1_partfun1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_83])).
% 2.81/1.42  tff(c_38, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.81/1.42  tff(c_124, plain, (![C_111, A_112, B_113]: (v1_partfun1(C_111, A_112) | ~v1_funct_2(C_111, A_112, B_113) | ~v1_funct_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | v1_xboole_0(B_113))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.81/1.42  tff(c_131, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_124])).
% 2.81/1.42  tff(c_138, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_131])).
% 2.81/1.42  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_96, c_138])).
% 2.81/1.42  tff(c_141, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_83])).
% 2.81/1.42  tff(c_153, plain, (![C_114, B_115, A_116]: (m1_subset_1(k1_funct_1(C_114, B_115), A_116) | ~r2_hidden(B_115, k1_relat_1(C_114)) | ~v1_funct_1(C_114) | ~v5_relat_1(C_114, A_116) | ~v1_relat_1(C_114))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.42  tff(c_155, plain, (![B_115, A_116]: (m1_subset_1(k1_funct_1('#skF_4', B_115), A_116) | ~r2_hidden(B_115, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_116) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_153])).
% 2.81/1.42  tff(c_162, plain, (![B_115, A_116]: (m1_subset_1(k1_funct_1('#skF_4', B_115), A_116) | ~r2_hidden(B_115, '#skF_2') | ~v5_relat_1('#skF_4', A_116))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_40, c_155])).
% 2.81/1.42  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.81/1.42  tff(c_63, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_55])).
% 2.81/1.42  tff(c_53, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_45])).
% 2.81/1.42  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.81/1.42  tff(c_28, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.81/1.42  tff(c_72, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_64])).
% 2.81/1.42  tff(c_80, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_74])).
% 2.81/1.42  tff(c_86, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_28, c_80])).
% 2.81/1.42  tff(c_226, plain, (![A_128, B_129, C_130]: (k7_partfun1(A_128, B_129, C_130)=k1_funct_1(B_129, C_130) | ~r2_hidden(C_130, k1_relat_1(B_129)) | ~v1_funct_1(B_129) | ~v5_relat_1(B_129, A_128) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.81/1.42  tff(c_230, plain, (![A_128, C_130]: (k7_partfun1(A_128, '#skF_5', C_130)=k1_funct_1('#skF_5', C_130) | ~r2_hidden(C_130, '#skF_1') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_128) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_226])).
% 2.81/1.42  tff(c_269, plain, (![A_136, C_137]: (k7_partfun1(A_136, '#skF_5', C_137)=k1_funct_1('#skF_5', C_137) | ~r2_hidden(C_137, '#skF_1') | ~v5_relat_1('#skF_5', A_136))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_34, c_230])).
% 2.81/1.42  tff(c_272, plain, (![A_136, A_1]: (k7_partfun1(A_136, '#skF_5', A_1)=k1_funct_1('#skF_5', A_1) | ~v5_relat_1('#skF_5', A_136) | v1_xboole_0('#skF_1') | ~m1_subset_1(A_1, '#skF_1'))), inference(resolution, [status(thm)], [c_2, c_269])).
% 2.81/1.42  tff(c_276, plain, (![A_138, A_139]: (k7_partfun1(A_138, '#skF_5', A_139)=k1_funct_1('#skF_5', A_139) | ~v5_relat_1('#skF_5', A_138) | ~m1_subset_1(A_139, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_272])).
% 2.81/1.42  tff(c_280, plain, (![A_140]: (k7_partfun1('#skF_3', '#skF_5', A_140)=k1_funct_1('#skF_5', A_140) | ~m1_subset_1(A_140, '#skF_1'))), inference(resolution, [status(thm)], [c_63, c_276])).
% 2.81/1.42  tff(c_288, plain, (![B_115]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_115))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_115)) | ~r2_hidden(B_115, '#skF_2') | ~v5_relat_1('#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_162, c_280])).
% 2.81/1.42  tff(c_292, plain, (![B_115]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_115))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_115)) | ~r2_hidden(B_115, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_288])).
% 2.81/1.42  tff(c_293, plain, (![A_141, B_142, C_143, D_144]: (k3_funct_2(A_141, B_142, C_143, D_144)=k1_funct_1(C_143, D_144) | ~m1_subset_1(D_144, A_141) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_2(C_143, A_141, B_142) | ~v1_funct_1(C_143) | v1_xboole_0(A_141))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.81/1.42  tff(c_303, plain, (![B_142, C_143]: (k3_funct_2('#skF_2', B_142, C_143, '#skF_6')=k1_funct_1(C_143, '#skF_6') | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_142))) | ~v1_funct_2(C_143, '#skF_2', B_142) | ~v1_funct_1(C_143) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_293])).
% 2.81/1.42  tff(c_321, plain, (![B_146, C_147]: (k3_funct_2('#skF_2', B_146, C_147, '#skF_6')=k1_funct_1(C_147, '#skF_6') | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_146))) | ~v1_funct_2(C_147, '#skF_2', B_146) | ~v1_funct_1(C_147))), inference(negUnitSimplification, [status(thm)], [c_42, c_303])).
% 2.81/1.42  tff(c_332, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_321])).
% 2.81/1.42  tff(c_337, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_332])).
% 2.81/1.42  tff(c_345, plain, (![F_153, E_148, A_149, B_152, D_151, C_150]: (k3_funct_2(B_152, C_150, k8_funct_2(B_152, A_149, C_150, D_151, E_148), F_153)=k1_funct_1(E_148, k3_funct_2(B_152, A_149, D_151, F_153)) | ~v1_partfun1(E_148, A_149) | ~m1_subset_1(F_153, B_152) | ~m1_subset_1(E_148, k1_zfmisc_1(k2_zfmisc_1(A_149, C_150))) | ~v1_funct_1(E_148) | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(B_152, A_149))) | ~v1_funct_2(D_151, B_152, A_149) | ~v1_funct_1(D_151) | v1_xboole_0(B_152) | v1_xboole_0(A_149))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.81/1.42  tff(c_355, plain, (![B_152, D_151, F_153]: (k3_funct_2(B_152, '#skF_3', k8_funct_2(B_152, '#skF_1', '#skF_3', D_151, '#skF_5'), F_153)=k1_funct_1('#skF_5', k3_funct_2(B_152, '#skF_1', D_151, F_153)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_153, B_152) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(B_152, '#skF_1'))) | ~v1_funct_2(D_151, B_152, '#skF_1') | ~v1_funct_1(D_151) | v1_xboole_0(B_152) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_345])).
% 2.81/1.42  tff(c_364, plain, (![B_152, D_151, F_153]: (k3_funct_2(B_152, '#skF_3', k8_funct_2(B_152, '#skF_1', '#skF_3', D_151, '#skF_5'), F_153)=k1_funct_1('#skF_5', k3_funct_2(B_152, '#skF_1', D_151, F_153)) | ~m1_subset_1(F_153, B_152) | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(B_152, '#skF_1'))) | ~v1_funct_2(D_151, B_152, '#skF_1') | ~v1_funct_1(D_151) | v1_xboole_0(B_152) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_355])).
% 2.81/1.42  tff(c_454, plain, (![B_174, D_175, F_176]: (k3_funct_2(B_174, '#skF_3', k8_funct_2(B_174, '#skF_1', '#skF_3', D_175, '#skF_5'), F_176)=k1_funct_1('#skF_5', k3_funct_2(B_174, '#skF_1', D_175, F_176)) | ~m1_subset_1(F_176, B_174) | ~m1_subset_1(D_175, k1_zfmisc_1(k2_zfmisc_1(B_174, '#skF_1'))) | ~v1_funct_2(D_175, B_174, '#skF_1') | ~v1_funct_1(D_175) | v1_xboole_0(B_174))), inference(negUnitSimplification, [status(thm)], [c_44, c_364])).
% 2.81/1.42  tff(c_465, plain, (![F_176]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_176)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_176)) | ~m1_subset_1(F_176, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_454])).
% 2.81/1.42  tff(c_471, plain, (![F_176]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_176)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_176)) | ~m1_subset_1(F_176, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_465])).
% 2.81/1.42  tff(c_473, plain, (![F_177]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_177)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_177)) | ~m1_subset_1(F_177, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_471])).
% 2.81/1.42  tff(c_26, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.81/1.42  tff(c_338, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_26])).
% 2.81/1.42  tff(c_479, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_473, c_338])).
% 2.81/1.42  tff(c_485, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_337, c_479])).
% 2.81/1.42  tff(c_490, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_292, c_485])).
% 2.81/1.42  tff(c_493, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_2, c_490])).
% 2.81/1.42  tff(c_496, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_493])).
% 2.81/1.42  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_496])).
% 2.81/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.42  
% 2.81/1.42  Inference rules
% 2.81/1.42  ----------------------
% 2.81/1.42  #Ref     : 0
% 2.81/1.42  #Sup     : 90
% 2.81/1.42  #Fact    : 0
% 2.81/1.42  #Define  : 0
% 2.81/1.42  #Split   : 8
% 2.81/1.42  #Chain   : 0
% 2.81/1.42  #Close   : 0
% 2.81/1.42  
% 2.81/1.42  Ordering : KBO
% 2.81/1.42  
% 2.81/1.42  Simplification rules
% 2.81/1.42  ----------------------
% 2.81/1.42  #Subsume      : 19
% 2.81/1.42  #Demod        : 55
% 2.81/1.42  #Tautology    : 17
% 2.81/1.42  #SimpNegUnit  : 13
% 2.81/1.42  #BackRed      : 1
% 2.81/1.42  
% 2.81/1.42  #Partial instantiations: 0
% 2.81/1.42  #Strategies tried      : 1
% 2.81/1.42  
% 2.81/1.42  Timing (in seconds)
% 2.81/1.42  ----------------------
% 2.81/1.42  Preprocessing        : 0.34
% 2.81/1.42  Parsing              : 0.18
% 2.81/1.42  CNF conversion       : 0.03
% 2.81/1.42  Main loop            : 0.29
% 2.81/1.43  Inferencing          : 0.11
% 2.81/1.43  Reduction            : 0.09
% 2.81/1.43  Demodulation         : 0.06
% 2.81/1.43  BG Simplification    : 0.02
% 2.81/1.43  Subsumption          : 0.05
% 2.81/1.43  Abstraction          : 0.02
% 2.81/1.43  MUC search           : 0.00
% 2.81/1.43  Cooper               : 0.00
% 2.81/1.43  Total                : 0.67
% 2.81/1.43  Index Insertion      : 0.00
% 2.81/1.43  Index Deletion       : 0.00
% 2.81/1.43  Index Matching       : 0.00
% 2.81/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
