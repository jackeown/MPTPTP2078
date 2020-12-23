%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:13 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 271 expanded)
%              Number of leaves         :   37 ( 112 expanded)
%              Depth                    :   16
%              Number of atoms          :  261 (1136 expanded)
%              Number of equality atoms :   35 ( 118 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_170,negated_conjecture,(
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

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_131,axiom,(
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

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_105,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( m1_subset_1(D,A)
                 => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

tff(c_36,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_263,plain,(
    ! [A_143,B_144,C_145,D_146] :
      ( k3_funct_2(A_143,B_144,C_145,D_146) = k1_funct_1(C_145,D_146)
      | ~ m1_subset_1(D_146,A_143)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | ~ v1_funct_2(C_145,A_143,B_144)
      | ~ v1_funct_1(C_145)
      | v1_xboole_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_277,plain,(
    ! [B_144,C_145] :
      ( k3_funct_2('#skF_2',B_144,C_145,'#skF_6') = k1_funct_1(C_145,'#skF_6')
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_144)))
      | ~ v1_funct_2(C_145,'#skF_2',B_144)
      | ~ v1_funct_1(C_145)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_263])).

tff(c_351,plain,(
    ! [B_155,C_156] :
      ( k3_funct_2('#skF_2',B_155,C_156,'#skF_6') = k1_funct_1(C_156,'#skF_6')
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_155)))
      | ~ v1_funct_2(C_156,'#skF_2',B_155)
      | ~ v1_funct_1(C_156) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_277])).

tff(c_358,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_351])).

tff(c_362,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_358])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_34,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_482,plain,(
    ! [B_166,A_167,D_171,E_170,C_168,F_169] :
      ( k3_funct_2(B_166,C_168,k8_funct_2(B_166,A_167,C_168,D_171,E_170),F_169) = k1_funct_1(E_170,k3_funct_2(B_166,A_167,D_171,F_169))
      | ~ v1_partfun1(E_170,A_167)
      | ~ m1_subset_1(F_169,B_166)
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(A_167,C_168)))
      | ~ v1_funct_1(E_170)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(k2_zfmisc_1(B_166,A_167)))
      | ~ v1_funct_2(D_171,B_166,A_167)
      | ~ v1_funct_1(D_171)
      | v1_xboole_0(B_166)
      | v1_xboole_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_493,plain,(
    ! [B_166,D_171,F_169] :
      ( k3_funct_2(B_166,'#skF_3',k8_funct_2(B_166,'#skF_1','#skF_3',D_171,'#skF_5'),F_169) = k1_funct_1('#skF_5',k3_funct_2(B_166,'#skF_1',D_171,F_169))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_169,B_166)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_171,k1_zfmisc_1(k2_zfmisc_1(B_166,'#skF_1')))
      | ~ v1_funct_2(D_171,B_166,'#skF_1')
      | ~ v1_funct_1(D_171)
      | v1_xboole_0(B_166)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_482])).

tff(c_506,plain,(
    ! [B_166,D_171,F_169] :
      ( k3_funct_2(B_166,'#skF_3',k8_funct_2(B_166,'#skF_1','#skF_3',D_171,'#skF_5'),F_169) = k1_funct_1('#skF_5',k3_funct_2(B_166,'#skF_1',D_171,F_169))
      | ~ m1_subset_1(F_169,B_166)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(k2_zfmisc_1(B_166,'#skF_1')))
      | ~ v1_funct_2(D_171,B_166,'#skF_1')
      | ~ v1_funct_1(D_171)
      | v1_xboole_0(B_166)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_493])).

tff(c_931,plain,(
    ! [B_196,D_197,F_198] :
      ( k3_funct_2(B_196,'#skF_3',k8_funct_2(B_196,'#skF_1','#skF_3',D_197,'#skF_5'),F_198) = k1_funct_1('#skF_5',k3_funct_2(B_196,'#skF_1',D_197,F_198))
      | ~ m1_subset_1(F_198,B_196)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(B_196,'#skF_1')))
      | ~ v1_funct_2(D_197,B_196,'#skF_1')
      | ~ v1_funct_1(D_197)
      | v1_xboole_0(B_196) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_506])).

tff(c_951,plain,(
    ! [F_198] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_198) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_198))
      | ~ m1_subset_1(F_198,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_931])).

tff(c_963,plain,(
    ! [F_198] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_198) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_198))
      | ~ m1_subset_1(F_198,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_951])).

tff(c_965,plain,(
    ! [F_199] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_199) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_199))
      | ~ m1_subset_1(F_199,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_963])).

tff(c_108,plain,(
    ! [C_120,A_121,B_122] :
      ( ~ v1_partfun1(C_120,A_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ v1_xboole_0(B_122)
      | v1_xboole_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_114,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_108])).

tff(c_119,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_114])).

tff(c_120,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_119])).

tff(c_60,plain,(
    ! [C_107,B_108,A_109] :
      ( v5_relat_1(C_107,B_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_68,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_60])).

tff(c_51,plain,(
    ! [C_104,A_105,B_106] :
      ( v1_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_51])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [C_114,A_115,B_116] :
      ( v4_relat_1(C_114,A_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_75])).

tff(c_85,plain,(
    ! [B_118,A_119] :
      ( k1_relat_1(B_118) = A_119
      | ~ v1_partfun1(B_118,A_119)
      | ~ v4_relat_1(B_118,A_119)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_88,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_83,c_85])).

tff(c_94,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_34,c_88])).

tff(c_121,plain,(
    ! [B_123,A_124] :
      ( v1_funct_2(B_123,k1_relat_1(B_123),A_124)
      | ~ r1_tarski(k2_relat_1(B_123),A_124)
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_124,plain,(
    ! [A_124] :
      ( v1_funct_2('#skF_5','#skF_1',A_124)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_124)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_121])).

tff(c_127,plain,(
    ! [A_125] :
      ( v1_funct_2('#skF_5','#skF_1',A_125)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_40,c_124])).

tff(c_131,plain,(
    ! [A_1] :
      ( v1_funct_2('#skF_5','#skF_1',A_1)
      | ~ v5_relat_1('#skF_5',A_1)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4,c_127])).

tff(c_134,plain,(
    ! [A_1] :
      ( v1_funct_2('#skF_5','#skF_1',A_1)
      | ~ v5_relat_1('#skF_5',A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_131])).

tff(c_193,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( m1_subset_1(k3_funct_2(A_132,B_133,C_134,D_135),B_133)
      | ~ m1_subset_1(D_135,A_132)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ v1_funct_2(C_134,A_132,B_133)
      | ~ v1_funct_1(C_134)
      | v1_xboole_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_201,plain,(
    ! [D_135] :
      ( m1_subset_1(k3_funct_2('#skF_1','#skF_3','#skF_5',D_135),'#skF_3')
      | ~ m1_subset_1(D_135,'#skF_1')
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_193])).

tff(c_213,plain,(
    ! [D_135] :
      ( m1_subset_1(k3_funct_2('#skF_1','#skF_3','#skF_5',D_135),'#skF_3')
      | ~ m1_subset_1(D_135,'#skF_1')
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_201])).

tff(c_214,plain,(
    ! [D_135] :
      ( m1_subset_1(k3_funct_2('#skF_1','#skF_3','#skF_5',D_135),'#skF_3')
      | ~ m1_subset_1(D_135,'#skF_1')
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_213])).

tff(c_228,plain,(
    ~ v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_231,plain,(
    ~ v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_228])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_231])).

tff(c_237,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_199,plain,(
    ! [D_135] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_135),'#skF_1')
      | ~ m1_subset_1(D_135,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_193])).

tff(c_209,plain,(
    ! [D_135] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_135),'#skF_1')
      | ~ m1_subset_1(D_135,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_199])).

tff(c_210,plain,(
    ! [D_135] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_135),'#skF_1')
      | ~ m1_subset_1(D_135,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_209])).

tff(c_367,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_210])).

tff(c_371,plain,(
    m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_367])).

tff(c_20,plain,(
    ! [A_19,B_20,C_21,D_22] :
      ( k3_funct_2(A_19,B_20,C_21,D_22) = k1_funct_1(C_21,D_22)
      | ~ m1_subset_1(D_22,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(C_21,A_19,B_20)
      | ~ v1_funct_1(C_21)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_407,plain,(
    ! [B_20,C_21] :
      ( k3_funct_2('#skF_1',B_20,C_21,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_21,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_20)))
      | ~ v1_funct_2(C_21,'#skF_1',B_20)
      | ~ v1_funct_1(C_21)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_371,c_20])).

tff(c_431,plain,(
    ! [B_163,C_164] :
      ( k3_funct_2('#skF_1',B_163,C_164,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_164,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_163)))
      | ~ v1_funct_2(C_164,'#skF_1',B_163)
      | ~ v1_funct_1(C_164) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_407])).

tff(c_441,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_431])).

tff(c_448,plain,(
    k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_237,c_441])).

tff(c_22,plain,(
    ! [A_23,B_31,C_35,D_37] :
      ( k3_funct_2(A_23,B_31,C_35,D_37) = k7_partfun1(B_31,C_35,D_37)
      | ~ m1_subset_1(D_37,A_23)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_23,B_31)))
      | ~ v1_funct_2(C_35,A_23,B_31)
      | ~ v1_funct_1(C_35)
      | v1_xboole_0(B_31)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_405,plain,(
    ! [B_31,C_35] :
      ( k3_funct_2('#skF_1',B_31,C_35,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_31,C_35,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_31)))
      | ~ v1_funct_2(C_35,'#skF_1',B_31)
      | ~ v1_funct_1(C_35)
      | v1_xboole_0(B_31)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_371,c_22])).

tff(c_591,plain,(
    ! [B_174,C_175] :
      ( k3_funct_2('#skF_1',B_174,C_175,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_174,C_175,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_174)))
      | ~ v1_funct_2(C_175,'#skF_1',B_174)
      | ~ v1_funct_1(C_175)
      | v1_xboole_0(B_174) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_405])).

tff(c_605,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_591])).

tff(c_613,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_237,c_448,c_605])).

tff(c_614,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_613])).

tff(c_32,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_363,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_32])).

tff(c_615,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_363])).

tff(c_971,plain,
    ( k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_965,c_615])).

tff(c_978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_362,c_971])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:18:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.52  
% 3.43/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.43/1.52  
% 3.43/1.52  %Foreground sorts:
% 3.43/1.52  
% 3.43/1.52  
% 3.43/1.52  %Background operators:
% 3.43/1.52  
% 3.43/1.52  
% 3.43/1.52  %Foreground operators:
% 3.43/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.43/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.43/1.52  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.43/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.43/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.43/1.52  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.43/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.43/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.52  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.43/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.43/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.43/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.43/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.43/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.43/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.43/1.52  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.43/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.43/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.52  
% 3.65/1.54  tff(f_170, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_funct_2)).
% 3.65/1.54  tff(f_86, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.65/1.54  tff(f_131, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 3.65/1.54  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_partfun1)).
% 3.65/1.54  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.65/1.54  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.65/1.54  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.65/1.54  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.65/1.54  tff(f_143, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.65/1.54  tff(f_73, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 3.65/1.54  tff(f_105, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 3.65/1.54  tff(c_36, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.65/1.54  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.65/1.54  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.65/1.54  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.65/1.54  tff(c_48, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.65/1.54  tff(c_263, plain, (![A_143, B_144, C_145, D_146]: (k3_funct_2(A_143, B_144, C_145, D_146)=k1_funct_1(C_145, D_146) | ~m1_subset_1(D_146, A_143) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | ~v1_funct_2(C_145, A_143, B_144) | ~v1_funct_1(C_145) | v1_xboole_0(A_143))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.65/1.54  tff(c_277, plain, (![B_144, C_145]: (k3_funct_2('#skF_2', B_144, C_145, '#skF_6')=k1_funct_1(C_145, '#skF_6') | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_144))) | ~v1_funct_2(C_145, '#skF_2', B_144) | ~v1_funct_1(C_145) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_263])).
% 3.65/1.54  tff(c_351, plain, (![B_155, C_156]: (k3_funct_2('#skF_2', B_155, C_156, '#skF_6')=k1_funct_1(C_156, '#skF_6') | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_155))) | ~v1_funct_2(C_156, '#skF_2', B_155) | ~v1_funct_1(C_156))), inference(negUnitSimplification, [status(thm)], [c_48, c_277])).
% 3.65/1.54  tff(c_358, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_351])).
% 3.65/1.54  tff(c_362, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_358])).
% 3.65/1.54  tff(c_50, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.65/1.54  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.65/1.54  tff(c_34, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.65/1.54  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.65/1.54  tff(c_482, plain, (![B_166, A_167, D_171, E_170, C_168, F_169]: (k3_funct_2(B_166, C_168, k8_funct_2(B_166, A_167, C_168, D_171, E_170), F_169)=k1_funct_1(E_170, k3_funct_2(B_166, A_167, D_171, F_169)) | ~v1_partfun1(E_170, A_167) | ~m1_subset_1(F_169, B_166) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(A_167, C_168))) | ~v1_funct_1(E_170) | ~m1_subset_1(D_171, k1_zfmisc_1(k2_zfmisc_1(B_166, A_167))) | ~v1_funct_2(D_171, B_166, A_167) | ~v1_funct_1(D_171) | v1_xboole_0(B_166) | v1_xboole_0(A_167))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.65/1.54  tff(c_493, plain, (![B_166, D_171, F_169]: (k3_funct_2(B_166, '#skF_3', k8_funct_2(B_166, '#skF_1', '#skF_3', D_171, '#skF_5'), F_169)=k1_funct_1('#skF_5', k3_funct_2(B_166, '#skF_1', D_171, F_169)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_169, B_166) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_171, k1_zfmisc_1(k2_zfmisc_1(B_166, '#skF_1'))) | ~v1_funct_2(D_171, B_166, '#skF_1') | ~v1_funct_1(D_171) | v1_xboole_0(B_166) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_482])).
% 3.65/1.54  tff(c_506, plain, (![B_166, D_171, F_169]: (k3_funct_2(B_166, '#skF_3', k8_funct_2(B_166, '#skF_1', '#skF_3', D_171, '#skF_5'), F_169)=k1_funct_1('#skF_5', k3_funct_2(B_166, '#skF_1', D_171, F_169)) | ~m1_subset_1(F_169, B_166) | ~m1_subset_1(D_171, k1_zfmisc_1(k2_zfmisc_1(B_166, '#skF_1'))) | ~v1_funct_2(D_171, B_166, '#skF_1') | ~v1_funct_1(D_171) | v1_xboole_0(B_166) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_493])).
% 3.65/1.54  tff(c_931, plain, (![B_196, D_197, F_198]: (k3_funct_2(B_196, '#skF_3', k8_funct_2(B_196, '#skF_1', '#skF_3', D_197, '#skF_5'), F_198)=k1_funct_1('#skF_5', k3_funct_2(B_196, '#skF_1', D_197, F_198)) | ~m1_subset_1(F_198, B_196) | ~m1_subset_1(D_197, k1_zfmisc_1(k2_zfmisc_1(B_196, '#skF_1'))) | ~v1_funct_2(D_197, B_196, '#skF_1') | ~v1_funct_1(D_197) | v1_xboole_0(B_196))), inference(negUnitSimplification, [status(thm)], [c_50, c_506])).
% 3.65/1.54  tff(c_951, plain, (![F_198]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_198)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_198)) | ~m1_subset_1(F_198, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_931])).
% 3.65/1.54  tff(c_963, plain, (![F_198]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_198)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_198)) | ~m1_subset_1(F_198, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_951])).
% 3.65/1.54  tff(c_965, plain, (![F_199]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_199)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_199)) | ~m1_subset_1(F_199, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_963])).
% 3.65/1.54  tff(c_108, plain, (![C_120, A_121, B_122]: (~v1_partfun1(C_120, A_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~v1_xboole_0(B_122) | v1_xboole_0(A_121))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.65/1.54  tff(c_114, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_108])).
% 3.65/1.54  tff(c_119, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_114])).
% 3.65/1.54  tff(c_120, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_119])).
% 3.65/1.54  tff(c_60, plain, (![C_107, B_108, A_109]: (v5_relat_1(C_107, B_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.65/1.54  tff(c_68, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_60])).
% 3.65/1.54  tff(c_51, plain, (![C_104, A_105, B_106]: (v1_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.65/1.54  tff(c_59, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_51])).
% 3.65/1.54  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.65/1.54  tff(c_75, plain, (![C_114, A_115, B_116]: (v4_relat_1(C_114, A_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.65/1.54  tff(c_83, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_75])).
% 3.65/1.54  tff(c_85, plain, (![B_118, A_119]: (k1_relat_1(B_118)=A_119 | ~v1_partfun1(B_118, A_119) | ~v4_relat_1(B_118, A_119) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.65/1.54  tff(c_88, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_83, c_85])).
% 3.65/1.54  tff(c_94, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_34, c_88])).
% 3.65/1.54  tff(c_121, plain, (![B_123, A_124]: (v1_funct_2(B_123, k1_relat_1(B_123), A_124) | ~r1_tarski(k2_relat_1(B_123), A_124) | ~v1_funct_1(B_123) | ~v1_relat_1(B_123))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.65/1.54  tff(c_124, plain, (![A_124]: (v1_funct_2('#skF_5', '#skF_1', A_124) | ~r1_tarski(k2_relat_1('#skF_5'), A_124) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_121])).
% 3.65/1.54  tff(c_127, plain, (![A_125]: (v1_funct_2('#skF_5', '#skF_1', A_125) | ~r1_tarski(k2_relat_1('#skF_5'), A_125))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_40, c_124])).
% 3.65/1.54  tff(c_131, plain, (![A_1]: (v1_funct_2('#skF_5', '#skF_1', A_1) | ~v5_relat_1('#skF_5', A_1) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_127])).
% 3.65/1.54  tff(c_134, plain, (![A_1]: (v1_funct_2('#skF_5', '#skF_1', A_1) | ~v5_relat_1('#skF_5', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_131])).
% 3.65/1.54  tff(c_193, plain, (![A_132, B_133, C_134, D_135]: (m1_subset_1(k3_funct_2(A_132, B_133, C_134, D_135), B_133) | ~m1_subset_1(D_135, A_132) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~v1_funct_2(C_134, A_132, B_133) | ~v1_funct_1(C_134) | v1_xboole_0(A_132))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.65/1.54  tff(c_201, plain, (![D_135]: (m1_subset_1(k3_funct_2('#skF_1', '#skF_3', '#skF_5', D_135), '#skF_3') | ~m1_subset_1(D_135, '#skF_1') | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_193])).
% 3.65/1.54  tff(c_213, plain, (![D_135]: (m1_subset_1(k3_funct_2('#skF_1', '#skF_3', '#skF_5', D_135), '#skF_3') | ~m1_subset_1(D_135, '#skF_1') | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_201])).
% 3.65/1.54  tff(c_214, plain, (![D_135]: (m1_subset_1(k3_funct_2('#skF_1', '#skF_3', '#skF_5', D_135), '#skF_3') | ~m1_subset_1(D_135, '#skF_1') | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_213])).
% 3.65/1.54  tff(c_228, plain, (~v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_214])).
% 3.65/1.54  tff(c_231, plain, (~v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_134, c_228])).
% 3.65/1.54  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_231])).
% 3.65/1.54  tff(c_237, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_214])).
% 3.65/1.54  tff(c_199, plain, (![D_135]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_135), '#skF_1') | ~m1_subset_1(D_135, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_193])).
% 3.65/1.54  tff(c_209, plain, (![D_135]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_135), '#skF_1') | ~m1_subset_1(D_135, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_199])).
% 3.65/1.54  tff(c_210, plain, (![D_135]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_135), '#skF_1') | ~m1_subset_1(D_135, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_209])).
% 3.65/1.54  tff(c_367, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_362, c_210])).
% 3.65/1.54  tff(c_371, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_367])).
% 3.65/1.54  tff(c_20, plain, (![A_19, B_20, C_21, D_22]: (k3_funct_2(A_19, B_20, C_21, D_22)=k1_funct_1(C_21, D_22) | ~m1_subset_1(D_22, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(C_21, A_19, B_20) | ~v1_funct_1(C_21) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.65/1.54  tff(c_407, plain, (![B_20, C_21]: (k3_funct_2('#skF_1', B_20, C_21, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_21, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_20))) | ~v1_funct_2(C_21, '#skF_1', B_20) | ~v1_funct_1(C_21) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_371, c_20])).
% 3.65/1.54  tff(c_431, plain, (![B_163, C_164]: (k3_funct_2('#skF_1', B_163, C_164, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_164, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_163))) | ~v1_funct_2(C_164, '#skF_1', B_163) | ~v1_funct_1(C_164))), inference(negUnitSimplification, [status(thm)], [c_50, c_407])).
% 3.65/1.54  tff(c_441, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_431])).
% 3.65/1.54  tff(c_448, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_237, c_441])).
% 3.65/1.54  tff(c_22, plain, (![A_23, B_31, C_35, D_37]: (k3_funct_2(A_23, B_31, C_35, D_37)=k7_partfun1(B_31, C_35, D_37) | ~m1_subset_1(D_37, A_23) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_23, B_31))) | ~v1_funct_2(C_35, A_23, B_31) | ~v1_funct_1(C_35) | v1_xboole_0(B_31) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.65/1.54  tff(c_405, plain, (![B_31, C_35]: (k3_funct_2('#skF_1', B_31, C_35, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_31, C_35, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_31))) | ~v1_funct_2(C_35, '#skF_1', B_31) | ~v1_funct_1(C_35) | v1_xboole_0(B_31) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_371, c_22])).
% 3.65/1.54  tff(c_591, plain, (![B_174, C_175]: (k3_funct_2('#skF_1', B_174, C_175, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_174, C_175, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_174))) | ~v1_funct_2(C_175, '#skF_1', B_174) | ~v1_funct_1(C_175) | v1_xboole_0(B_174))), inference(negUnitSimplification, [status(thm)], [c_50, c_405])).
% 3.65/1.54  tff(c_605, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_591])).
% 3.65/1.54  tff(c_613, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_237, c_448, c_605])).
% 3.65/1.54  tff(c_614, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_120, c_613])).
% 3.65/1.54  tff(c_32, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.65/1.54  tff(c_363, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_362, c_32])).
% 3.65/1.54  tff(c_615, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_614, c_363])).
% 3.65/1.54  tff(c_971, plain, (k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_965, c_615])).
% 3.65/1.54  tff(c_978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_362, c_971])).
% 3.65/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.54  
% 3.65/1.54  Inference rules
% 3.65/1.54  ----------------------
% 3.65/1.54  #Ref     : 0
% 3.65/1.54  #Sup     : 186
% 3.65/1.54  #Fact    : 0
% 3.65/1.54  #Define  : 0
% 3.65/1.54  #Split   : 6
% 3.65/1.54  #Chain   : 0
% 3.65/1.54  #Close   : 0
% 3.65/1.54  
% 3.65/1.54  Ordering : KBO
% 3.65/1.54  
% 3.65/1.54  Simplification rules
% 3.65/1.54  ----------------------
% 3.65/1.54  #Subsume      : 34
% 3.65/1.54  #Demod        : 129
% 3.65/1.54  #Tautology    : 44
% 3.65/1.54  #SimpNegUnit  : 33
% 3.65/1.54  #BackRed      : 2
% 3.65/1.54  
% 3.65/1.54  #Partial instantiations: 0
% 3.65/1.54  #Strategies tried      : 1
% 3.65/1.54  
% 3.65/1.54  Timing (in seconds)
% 3.65/1.54  ----------------------
% 3.65/1.55  Preprocessing        : 0.35
% 3.65/1.55  Parsing              : 0.18
% 3.65/1.55  CNF conversion       : 0.03
% 3.65/1.55  Main loop            : 0.42
% 3.65/1.55  Inferencing          : 0.15
% 3.65/1.55  Reduction            : 0.14
% 3.65/1.55  Demodulation         : 0.10
% 3.65/1.55  BG Simplification    : 0.02
% 3.65/1.55  Subsumption          : 0.07
% 3.65/1.55  Abstraction          : 0.03
% 3.65/1.55  MUC search           : 0.00
% 3.65/1.55  Cooper               : 0.00
% 3.65/1.55  Total                : 0.82
% 3.65/1.55  Index Insertion      : 0.00
% 3.65/1.55  Index Deletion       : 0.00
% 3.65/1.55  Index Matching       : 0.00
% 3.65/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
