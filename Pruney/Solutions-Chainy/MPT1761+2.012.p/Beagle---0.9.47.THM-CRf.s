%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:10 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 127 expanded)
%              Number of leaves         :   38 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  195 ( 667 expanded)
%              Number of equality atoms :   26 (  53 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ( r2_hidden(F,u1_struct_0(C))
                               => k3_funct_2(u1_struct_0(D),u1_struct_0(B),E,F) = k1_funct_1(k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tmap_1)).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_26,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( v1_relat_1(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_32,c_8])).

tff(c_77,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_71])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_30,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_34,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_108,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( k2_partfun1(A_137,B_138,C_139,D_140) = k7_relat_1(C_139,D_140)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138)))
      | ~ v1_funct_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_110,plain,(
    ! [D_140] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_140) = k7_relat_1('#skF_5',D_140)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_108])).

tff(c_116,plain,(
    ! [D_140] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_140) = k7_relat_1('#skF_5',D_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_110])).

tff(c_191,plain,(
    ! [C_162,A_159,D_158,B_160,E_161] :
      ( k3_tmap_1(A_159,B_160,C_162,D_158,E_161) = k2_partfun1(u1_struct_0(C_162),u1_struct_0(B_160),E_161,u1_struct_0(D_158))
      | ~ m1_pre_topc(D_158,C_162)
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_162),u1_struct_0(B_160))))
      | ~ v1_funct_2(E_161,u1_struct_0(C_162),u1_struct_0(B_160))
      | ~ v1_funct_1(E_161)
      | ~ m1_pre_topc(D_158,A_159)
      | ~ m1_pre_topc(C_162,A_159)
      | ~ l1_pre_topc(B_160)
      | ~ v2_pre_topc(B_160)
      | v2_struct_0(B_160)
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_193,plain,(
    ! [A_159,D_158] :
      ( k3_tmap_1(A_159,'#skF_2','#skF_4',D_158,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_158))
      | ~ m1_pre_topc(D_158,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_158,A_159)
      | ~ m1_pre_topc('#skF_4',A_159)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(resolution,[status(thm)],[c_32,c_191])).

tff(c_199,plain,(
    ! [D_158,A_159] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_158)) = k3_tmap_1(A_159,'#skF_2','#skF_4',D_158,'#skF_5')
      | ~ m1_pre_topc(D_158,'#skF_4')
      | ~ m1_pre_topc(D_158,A_159)
      | ~ m1_pre_topc('#skF_4',A_159)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_34,c_116,c_193])).

tff(c_203,plain,(
    ! [D_163,A_164] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_163)) = k3_tmap_1(A_164,'#skF_2','#skF_4',D_163,'#skF_5')
      | ~ m1_pre_topc(D_163,'#skF_4')
      | ~ m1_pre_topc(D_163,A_164)
      | ~ m1_pre_topc('#skF_4',A_164)
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_199])).

tff(c_209,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_203])).

tff(c_220,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_38,c_30,c_209])).

tff(c_221,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_220])).

tff(c_12,plain,(
    ! [C_13,B_12,A_11] :
      ( k1_funct_1(k7_relat_1(C_13,B_12),A_11) = k1_funct_1(C_13,A_11)
      | ~ r2_hidden(A_11,B_12)
      | ~ v1_funct_1(C_13)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_225,plain,(
    ! [A_11] :
      ( k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),A_11) = k1_funct_1('#skF_5',A_11)
      | ~ r2_hidden(A_11,u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_12])).

tff(c_232,plain,(
    ! [A_165] :
      ( k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),A_165) = k1_funct_1('#skF_5',A_165)
      | ~ r2_hidden(A_165,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_36,c_225])).

tff(c_236,plain,(
    k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_232])).

tff(c_24,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') != k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_237,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') != k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_24])).

tff(c_134,plain,(
    ! [B_149,C_150,A_151] :
      ( r1_tarski(u1_struct_0(B_149),u1_struct_0(C_150))
      | ~ m1_pre_topc(B_149,C_150)
      | ~ m1_pre_topc(C_150,A_151)
      | ~ m1_pre_topc(B_149,A_151)
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_136,plain,(
    ! [B_149] :
      ( r1_tarski(u1_struct_0(B_149),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_149,'#skF_4')
      | ~ m1_pre_topc(B_149,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_134])).

tff(c_158,plain,(
    ! [B_156] :
      ( r1_tarski(u1_struct_0(B_156),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_156,'#skF_4')
      | ~ m1_pre_topc(B_156,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_136])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    ! [C_127,B_128,A_129] :
      ( ~ v1_xboole_0(C_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(C_127))
      | ~ r2_hidden(A_129,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_93,plain,(
    ! [B_130,A_131,A_132] :
      ( ~ v1_xboole_0(B_130)
      | ~ r2_hidden(A_131,A_132)
      | ~ r1_tarski(A_132,B_130) ) ),
    inference(resolution,[status(thm)],[c_4,c_86])).

tff(c_96,plain,(
    ! [B_130] :
      ( ~ v1_xboole_0(B_130)
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_130) ) ),
    inference(resolution,[status(thm)],[c_26,c_93])).

tff(c_164,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_158,c_96])).

tff(c_171,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_30,c_164])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_148,plain,(
    ! [A_152,B_153,C_154,D_155] :
      ( k3_funct_2(A_152,B_153,C_154,D_155) = k1_funct_1(C_154,D_155)
      | ~ m1_subset_1(D_155,A_152)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ v1_funct_2(C_154,A_152,B_153)
      | ~ v1_funct_1(C_154)
      | v1_xboole_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_157,plain,(
    ! [B_153,C_154] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_153,C_154,'#skF_6') = k1_funct_1(C_154,'#skF_6')
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_153)))
      | ~ v1_funct_2(C_154,u1_struct_0('#skF_4'),B_153)
      | ~ v1_funct_1(C_154)
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_28,c_148])).

tff(c_243,plain,(
    ! [B_166,C_167] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_166,C_167,'#skF_6') = k1_funct_1(C_167,'#skF_6')
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_166)))
      | ~ v1_funct_2(C_167,u1_struct_0('#skF_4'),B_166)
      | ~ v1_funct_1(C_167) ) ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_157])).

tff(c_246,plain,
    ( k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_243])).

tff(c_253,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_246])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.30  
% 2.25/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.30  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.25/1.30  
% 2.25/1.30  %Foreground sorts:
% 2.25/1.30  
% 2.25/1.30  
% 2.25/1.30  %Background operators:
% 2.25/1.30  
% 2.25/1.30  
% 2.25/1.30  %Foreground operators:
% 2.25/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.25/1.30  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.25/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.25/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.25/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.25/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.25/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.25/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.25/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.25/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.25/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.30  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.25/1.30  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.25/1.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.25/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.25/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.25/1.30  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.25/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.30  
% 2.58/1.32  tff(f_162, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, F) = k1_funct_1(k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tmap_1)).
% 2.58/1.32  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.58/1.32  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.58/1.32  tff(f_59, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.58/1.32  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.58/1.32  tff(f_53, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 2.58/1.32  tff(f_118, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.58/1.32  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.58/1.32  tff(f_36, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.58/1.32  tff(f_72, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.58/1.32  tff(c_26, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.58/1.32  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.58/1.32  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.58/1.32  tff(c_8, plain, (![B_8, A_6]: (v1_relat_1(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.58/1.32  tff(c_71, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_32, c_8])).
% 2.58/1.32  tff(c_77, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_71])).
% 2.58/1.32  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.58/1.32  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.58/1.32  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.58/1.32  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.58/1.32  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.58/1.32  tff(c_30, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.58/1.32  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.58/1.32  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.58/1.32  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.58/1.32  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.58/1.32  tff(c_34, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.58/1.32  tff(c_108, plain, (![A_137, B_138, C_139, D_140]: (k2_partfun1(A_137, B_138, C_139, D_140)=k7_relat_1(C_139, D_140) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))) | ~v1_funct_1(C_139))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.58/1.32  tff(c_110, plain, (![D_140]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_140)=k7_relat_1('#skF_5', D_140) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_108])).
% 2.58/1.32  tff(c_116, plain, (![D_140]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_140)=k7_relat_1('#skF_5', D_140))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_110])).
% 2.58/1.32  tff(c_191, plain, (![C_162, A_159, D_158, B_160, E_161]: (k3_tmap_1(A_159, B_160, C_162, D_158, E_161)=k2_partfun1(u1_struct_0(C_162), u1_struct_0(B_160), E_161, u1_struct_0(D_158)) | ~m1_pre_topc(D_158, C_162) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_162), u1_struct_0(B_160)))) | ~v1_funct_2(E_161, u1_struct_0(C_162), u1_struct_0(B_160)) | ~v1_funct_1(E_161) | ~m1_pre_topc(D_158, A_159) | ~m1_pre_topc(C_162, A_159) | ~l1_pre_topc(B_160) | ~v2_pre_topc(B_160) | v2_struct_0(B_160) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.58/1.32  tff(c_193, plain, (![A_159, D_158]: (k3_tmap_1(A_159, '#skF_2', '#skF_4', D_158, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_158)) | ~m1_pre_topc(D_158, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_158, A_159) | ~m1_pre_topc('#skF_4', A_159) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(resolution, [status(thm)], [c_32, c_191])).
% 2.58/1.32  tff(c_199, plain, (![D_158, A_159]: (k7_relat_1('#skF_5', u1_struct_0(D_158))=k3_tmap_1(A_159, '#skF_2', '#skF_4', D_158, '#skF_5') | ~m1_pre_topc(D_158, '#skF_4') | ~m1_pre_topc(D_158, A_159) | ~m1_pre_topc('#skF_4', A_159) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_34, c_116, c_193])).
% 2.58/1.32  tff(c_203, plain, (![D_163, A_164]: (k7_relat_1('#skF_5', u1_struct_0(D_163))=k3_tmap_1(A_164, '#skF_2', '#skF_4', D_163, '#skF_5') | ~m1_pre_topc(D_163, '#skF_4') | ~m1_pre_topc(D_163, A_164) | ~m1_pre_topc('#skF_4', A_164) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(negUnitSimplification, [status(thm)], [c_50, c_199])).
% 2.58/1.32  tff(c_209, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_203])).
% 2.58/1.32  tff(c_220, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_38, c_30, c_209])).
% 2.58/1.32  tff(c_221, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_220])).
% 2.58/1.32  tff(c_12, plain, (![C_13, B_12, A_11]: (k1_funct_1(k7_relat_1(C_13, B_12), A_11)=k1_funct_1(C_13, A_11) | ~r2_hidden(A_11, B_12) | ~v1_funct_1(C_13) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.58/1.32  tff(c_225, plain, (![A_11]: (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), A_11)=k1_funct_1('#skF_5', A_11) | ~r2_hidden(A_11, u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_221, c_12])).
% 2.58/1.32  tff(c_232, plain, (![A_165]: (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), A_165)=k1_funct_1('#skF_5', A_165) | ~r2_hidden(A_165, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_36, c_225])).
% 2.58/1.32  tff(c_236, plain, (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_232])).
% 2.58/1.32  tff(c_24, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')!=k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.58/1.32  tff(c_237, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')!=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_236, c_24])).
% 2.58/1.32  tff(c_134, plain, (![B_149, C_150, A_151]: (r1_tarski(u1_struct_0(B_149), u1_struct_0(C_150)) | ~m1_pre_topc(B_149, C_150) | ~m1_pre_topc(C_150, A_151) | ~m1_pre_topc(B_149, A_151) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.58/1.32  tff(c_136, plain, (![B_149]: (r1_tarski(u1_struct_0(B_149), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_149, '#skF_4') | ~m1_pre_topc(B_149, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_134])).
% 2.58/1.32  tff(c_158, plain, (![B_156]: (r1_tarski(u1_struct_0(B_156), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_156, '#skF_4') | ~m1_pre_topc(B_156, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_136])).
% 2.58/1.32  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.58/1.32  tff(c_86, plain, (![C_127, B_128, A_129]: (~v1_xboole_0(C_127) | ~m1_subset_1(B_128, k1_zfmisc_1(C_127)) | ~r2_hidden(A_129, B_128))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.58/1.32  tff(c_93, plain, (![B_130, A_131, A_132]: (~v1_xboole_0(B_130) | ~r2_hidden(A_131, A_132) | ~r1_tarski(A_132, B_130))), inference(resolution, [status(thm)], [c_4, c_86])).
% 2.58/1.32  tff(c_96, plain, (![B_130]: (~v1_xboole_0(B_130) | ~r1_tarski(u1_struct_0('#skF_3'), B_130))), inference(resolution, [status(thm)], [c_26, c_93])).
% 2.58/1.32  tff(c_164, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_158, c_96])).
% 2.58/1.32  tff(c_171, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_30, c_164])).
% 2.58/1.32  tff(c_28, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.58/1.32  tff(c_148, plain, (![A_152, B_153, C_154, D_155]: (k3_funct_2(A_152, B_153, C_154, D_155)=k1_funct_1(C_154, D_155) | ~m1_subset_1(D_155, A_152) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~v1_funct_2(C_154, A_152, B_153) | ~v1_funct_1(C_154) | v1_xboole_0(A_152))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.58/1.32  tff(c_157, plain, (![B_153, C_154]: (k3_funct_2(u1_struct_0('#skF_4'), B_153, C_154, '#skF_6')=k1_funct_1(C_154, '#skF_6') | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_153))) | ~v1_funct_2(C_154, u1_struct_0('#skF_4'), B_153) | ~v1_funct_1(C_154) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_28, c_148])).
% 2.58/1.32  tff(c_243, plain, (![B_166, C_167]: (k3_funct_2(u1_struct_0('#skF_4'), B_166, C_167, '#skF_6')=k1_funct_1(C_167, '#skF_6') | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_166))) | ~v1_funct_2(C_167, u1_struct_0('#skF_4'), B_166) | ~v1_funct_1(C_167))), inference(negUnitSimplification, [status(thm)], [c_171, c_157])).
% 2.58/1.32  tff(c_246, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_243])).
% 2.58/1.32  tff(c_253, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_246])).
% 2.58/1.32  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_253])).
% 2.58/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.32  
% 2.58/1.32  Inference rules
% 2.58/1.32  ----------------------
% 2.58/1.32  #Ref     : 0
% 2.58/1.32  #Sup     : 40
% 2.58/1.32  #Fact    : 0
% 2.58/1.32  #Define  : 0
% 2.58/1.32  #Split   : 6
% 2.58/1.32  #Chain   : 0
% 2.58/1.32  #Close   : 0
% 2.58/1.32  
% 2.58/1.32  Ordering : KBO
% 2.58/1.32  
% 2.58/1.32  Simplification rules
% 2.58/1.32  ----------------------
% 2.58/1.32  #Subsume      : 1
% 2.58/1.32  #Demod        : 31
% 2.58/1.32  #Tautology    : 13
% 2.58/1.32  #SimpNegUnit  : 6
% 2.58/1.32  #BackRed      : 1
% 2.58/1.32  
% 2.58/1.32  #Partial instantiations: 0
% 2.58/1.32  #Strategies tried      : 1
% 2.58/1.32  
% 2.58/1.32  Timing (in seconds)
% 2.58/1.32  ----------------------
% 2.58/1.33  Preprocessing        : 0.34
% 2.58/1.33  Parsing              : 0.18
% 2.58/1.33  CNF conversion       : 0.03
% 2.58/1.33  Main loop            : 0.22
% 2.58/1.33  Inferencing          : 0.08
% 2.58/1.33  Reduction            : 0.07
% 2.58/1.33  Demodulation         : 0.05
% 2.58/1.33  BG Simplification    : 0.02
% 2.58/1.33  Subsumption          : 0.03
% 2.58/1.33  Abstraction          : 0.01
% 2.58/1.33  MUC search           : 0.00
% 2.58/1.33  Cooper               : 0.00
% 2.58/1.33  Total                : 0.60
% 2.58/1.33  Index Insertion      : 0.00
% 2.58/1.33  Index Deletion       : 0.00
% 2.58/1.33  Index Matching       : 0.00
% 2.58/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
