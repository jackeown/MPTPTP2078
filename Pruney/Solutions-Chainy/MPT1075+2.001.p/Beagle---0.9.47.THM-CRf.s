%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:10 EST 2020

% Result     : Theorem 4.48s
% Output     : CNFRefutation 4.86s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 304 expanded)
%              Number of leaves         :   40 ( 125 expanded)
%              Depth                    :   12
%              Number of atoms          :  291 (1289 expanded)
%              Number of equality atoms :   57 ( 216 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_198,negated_conjecture,(
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
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k1_funct_1(E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_134,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_171,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_147,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_60,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_207,plain,(
    ! [C_124,A_125,B_126] :
      ( ~ v1_partfun1(C_124,A_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_xboole_0(B_126)
      | v1_xboole_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_210,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_207])).

tff(c_222,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_210])).

tff(c_223,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_222])).

tff(c_62,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_114,plain,(
    ! [C_90,A_91,B_92] :
      ( v1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_126,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_114])).

tff(c_140,plain,(
    ! [C_98,B_99,A_100] :
      ( v5_relat_1(C_98,B_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_154,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_140])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_235,plain,(
    ! [C_129,A_130,B_131] :
      ( v1_funct_2(C_129,A_130,B_131)
      | ~ v1_partfun1(C_129,A_130)
      | ~ v1_funct_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_238,plain,
    ( v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_235])).

tff(c_250,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_238])).

tff(c_256,plain,(
    ! [B_136,A_137,C_138] :
      ( k1_xboole_0 = B_136
      | k1_relset_1(A_137,B_136,C_138) = A_137
      | ~ v1_funct_2(C_138,A_137,B_136)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_259,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_256])).

tff(c_271,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_259])).

tff(c_294,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_390,plain,(
    ! [D_162,B_163,C_166,A_165,E_164] :
      ( v1_funct_2(k8_funct_2(A_165,B_163,C_166,D_162,E_164),A_165,C_166)
      | ~ m1_subset_1(E_164,k1_zfmisc_1(k2_zfmisc_1(B_163,C_166)))
      | ~ v1_funct_1(E_164)
      | ~ m1_subset_1(D_162,k1_zfmisc_1(k2_zfmisc_1(A_165,B_163)))
      | ~ v1_funct_2(D_162,A_165,B_163)
      | ~ v1_funct_1(D_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_521,plain,(
    ! [A_191,A_192,D_193,E_194] :
      ( v1_funct_2(k8_funct_2(A_191,A_192,k1_xboole_0,D_193,E_194),A_191,k1_xboole_0)
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(E_194)
      | ~ m1_subset_1(D_193,k1_zfmisc_1(k2_zfmisc_1(A_191,A_192)))
      | ~ v1_funct_2(D_193,A_191,A_192)
      | ~ v1_funct_1(D_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_390])).

tff(c_527,plain,(
    ! [E_194] :
      ( v1_funct_2(k8_funct_2('#skF_2','#skF_1',k1_xboole_0,'#skF_4',E_194),'#skF_2',k1_xboole_0)
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(E_194)
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_521])).

tff(c_543,plain,(
    ! [E_196] :
      ( v1_funct_2(k8_funct_2('#skF_2','#skF_1',k1_xboole_0,'#skF_4',E_196),'#skF_2',k1_xboole_0)
      | ~ m1_subset_1(E_196,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(E_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_527])).

tff(c_38,plain,(
    ! [C_30,A_28] :
      ( k1_xboole_0 = C_30
      | ~ v1_funct_2(C_30,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_80,plain,(
    ! [C_30,A_28] :
      ( k1_xboole_0 = C_30
      | ~ v1_funct_2(C_30,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_38])).

tff(c_546,plain,(
    ! [E_196] :
      ( k8_funct_2('#skF_2','#skF_1',k1_xboole_0,'#skF_4',E_196) = k1_xboole_0
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1',k1_xboole_0,'#skF_4',E_196),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(E_196,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(E_196) ) ),
    inference(resolution,[status(thm)],[c_543,c_80])).

tff(c_604,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_546])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_637,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_2])).

tff(c_639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_637])).

tff(c_641,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_546])).

tff(c_180,plain,(
    ! [A_113,B_114,C_115] :
      ( k2_relset_1(A_113,B_114,C_115) = k2_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_194,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_180])).

tff(c_583,plain,(
    ! [A_200,F_202,B_203,E_199,D_198,C_201] :
      ( k1_funct_1(k8_funct_2(B_203,C_201,A_200,D_198,E_199),F_202) = k1_funct_1(E_199,k1_funct_1(D_198,F_202))
      | k1_xboole_0 = B_203
      | ~ r1_tarski(k2_relset_1(B_203,C_201,D_198),k1_relset_1(C_201,A_200,E_199))
      | ~ m1_subset_1(F_202,B_203)
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(C_201,A_200)))
      | ~ v1_funct_1(E_199)
      | ~ m1_subset_1(D_198,k1_zfmisc_1(k2_zfmisc_1(B_203,C_201)))
      | ~ v1_funct_2(D_198,B_203,C_201)
      | ~ v1_funct_1(D_198)
      | v1_xboole_0(C_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_589,plain,(
    ! [A_200,E_199,F_202] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_200,'#skF_4',E_199),F_202) = k1_funct_1(E_199,k1_funct_1('#skF_4',F_202))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_200,E_199))
      | ~ m1_subset_1(F_202,'#skF_2')
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_200)))
      | ~ v1_funct_1(E_199)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_583])).

tff(c_599,plain,(
    ! [A_200,E_199,F_202] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_200,'#skF_4',E_199),F_202) = k1_funct_1(E_199,k1_funct_1('#skF_4',F_202))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_200,E_199))
      | ~ m1_subset_1(F_202,'#skF_2')
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_200)))
      | ~ v1_funct_1(E_199)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_589])).

tff(c_600,plain,(
    ! [A_200,E_199,F_202] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_200,'#skF_4',E_199),F_202) = k1_funct_1(E_199,k1_funct_1('#skF_4',F_202))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_200,E_199))
      | ~ m1_subset_1(F_202,'#skF_2')
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_200)))
      | ~ v1_funct_1(E_199) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_599])).

tff(c_643,plain,(
    ! [A_204,E_205,F_206] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_204,'#skF_4',E_205),F_206) = k1_funct_1(E_205,k1_funct_1('#skF_4',F_206))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_204,E_205))
      | ~ m1_subset_1(F_206,'#skF_2')
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_204)))
      | ~ v1_funct_1(E_205) ) ),
    inference(negUnitSimplification,[status(thm)],[c_641,c_600])).

tff(c_645,plain,(
    ! [F_206] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_206) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_206))
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_206,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_643])).

tff(c_650,plain,(
    ! [F_206] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_206) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_206))
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_206,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_645])).

tff(c_654,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_650])).

tff(c_657,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_654])).

tff(c_661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_154,c_657])).

tff(c_662,plain,(
    ! [F_206] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_206) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_206))
      | ~ m1_subset_1(F_206,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_650])).

tff(c_350,plain,(
    ! [C_155,B_152,A_154,D_151,E_153] :
      ( v1_funct_1(k8_funct_2(A_154,B_152,C_155,D_151,E_153))
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(B_152,C_155)))
      | ~ v1_funct_1(E_153)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(A_154,B_152)))
      | ~ v1_funct_2(D_151,A_154,B_152)
      | ~ v1_funct_1(D_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_352,plain,(
    ! [A_154,D_151] :
      ( v1_funct_1(k8_funct_2(A_154,'#skF_1','#skF_3',D_151,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(A_154,'#skF_1')))
      | ~ v1_funct_2(D_151,A_154,'#skF_1')
      | ~ v1_funct_1(D_151) ) ),
    inference(resolution,[status(thm)],[c_64,c_350])).

tff(c_379,plain,(
    ! [A_160,D_161] :
      ( v1_funct_1(k8_funct_2(A_160,'#skF_1','#skF_3',D_161,'#skF_5'))
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(A_160,'#skF_1')))
      | ~ v1_funct_2(D_161,A_160,'#skF_1')
      | ~ v1_funct_1(D_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_352])).

tff(c_382,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_379])).

tff(c_389,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_382])).

tff(c_392,plain,(
    ! [A_165,D_162] :
      ( v1_funct_2(k8_funct_2(A_165,'#skF_1','#skF_3',D_162,'#skF_5'),A_165,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_162,k1_zfmisc_1(k2_zfmisc_1(A_165,'#skF_1')))
      | ~ v1_funct_2(D_162,A_165,'#skF_1')
      | ~ v1_funct_1(D_162) ) ),
    inference(resolution,[status(thm)],[c_64,c_390])).

tff(c_416,plain,(
    ! [A_171,D_172] :
      ( v1_funct_2(k8_funct_2(A_171,'#skF_1','#skF_3',D_172,'#skF_5'),A_171,'#skF_3')
      | ~ m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(A_171,'#skF_1')))
      | ~ v1_funct_2(D_172,A_171,'#skF_1')
      | ~ v1_funct_1(D_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_392])).

tff(c_418,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_416])).

tff(c_424,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_418])).

tff(c_430,plain,(
    ! [C_182,A_181,B_179,D_178,E_180] :
      ( m1_subset_1(k8_funct_2(A_181,B_179,C_182,D_178,E_180),k1_zfmisc_1(k2_zfmisc_1(A_181,C_182)))
      | ~ m1_subset_1(E_180,k1_zfmisc_1(k2_zfmisc_1(B_179,C_182)))
      | ~ v1_funct_1(E_180)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(k2_zfmisc_1(A_181,B_179)))
      | ~ v1_funct_2(D_178,A_181,B_179)
      | ~ v1_funct_1(D_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_327,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( k3_funct_2(A_145,B_146,C_147,D_148) = k1_funct_1(C_147,D_148)
      | ~ m1_subset_1(D_148,A_145)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ v1_funct_2(C_147,A_145,B_146)
      | ~ v1_funct_1(C_147)
      | v1_xboole_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_333,plain,(
    ! [B_146,C_147] :
      ( k3_funct_2('#skF_2',B_146,C_147,'#skF_6') = k1_funct_1(C_147,'#skF_6')
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_146)))
      | ~ v1_funct_2(C_147,'#skF_2',B_146)
      | ~ v1_funct_1(C_147)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_62,c_327])).

tff(c_338,plain,(
    ! [B_146,C_147] :
      ( k3_funct_2('#skF_2',B_146,C_147,'#skF_6') = k1_funct_1(C_147,'#skF_6')
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_146)))
      | ~ v1_funct_2(C_147,'#skF_2',B_146)
      | ~ v1_funct_1(C_147) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_333])).

tff(c_1271,plain,(
    ! [C_383,B_384,D_385,E_386] :
      ( k3_funct_2('#skF_2',C_383,k8_funct_2('#skF_2',B_384,C_383,D_385,E_386),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2',B_384,C_383,D_385,E_386),'#skF_6')
      | ~ v1_funct_2(k8_funct_2('#skF_2',B_384,C_383,D_385,E_386),'#skF_2',C_383)
      | ~ v1_funct_1(k8_funct_2('#skF_2',B_384,C_383,D_385,E_386))
      | ~ m1_subset_1(E_386,k1_zfmisc_1(k2_zfmisc_1(B_384,C_383)))
      | ~ v1_funct_1(E_386)
      | ~ m1_subset_1(D_385,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_384)))
      | ~ v1_funct_2(D_385,'#skF_2',B_384)
      | ~ v1_funct_1(D_385) ) ),
    inference(resolution,[status(thm)],[c_430,c_338])).

tff(c_1278,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_424,c_1271])).

tff(c_1286,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_389,c_1278])).

tff(c_339,plain,(
    ! [B_149,C_150] :
      ( k3_funct_2('#skF_2',B_149,C_150,'#skF_6') = k1_funct_1(C_150,'#skF_6')
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_149)))
      | ~ v1_funct_2(C_150,'#skF_2',B_149)
      | ~ v1_funct_1(C_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_333])).

tff(c_342,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_339])).

tff(c_349,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_342])).

tff(c_58,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_366,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_58])).

tff(c_1287,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1286,c_366])).

tff(c_1294,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_1287])).

tff(c_1298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1294])).

tff(c_1299,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_1319,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_2])).

tff(c_1321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_1319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.48/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.90  
% 4.48/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.86/1.90  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.86/1.90  
% 4.86/1.90  %Foreground sorts:
% 4.86/1.90  
% 4.86/1.90  
% 4.86/1.90  %Background operators:
% 4.86/1.90  
% 4.86/1.90  
% 4.86/1.90  %Foreground operators:
% 4.86/1.90  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.86/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.86/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.86/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.86/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.86/1.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.86/1.90  tff('#skF_5', type, '#skF_5': $i).
% 4.86/1.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.86/1.90  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.86/1.90  tff('#skF_6', type, '#skF_6': $i).
% 4.86/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.86/1.90  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.86/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.86/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.86/1.90  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.86/1.90  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.86/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.86/1.90  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.86/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.86/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.86/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.86/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.86/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.86/1.90  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.86/1.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.86/1.90  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.86/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.86/1.90  
% 4.86/1.92  tff(f_198, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 4.86/1.92  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_partfun1)).
% 4.86/1.92  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.86/1.92  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.86/1.92  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.86/1.92  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 4.86/1.92  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.86/1.92  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.86/1.92  tff(f_134, axiom, (![A, B, C, D, E]: (((((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(E)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v1_funct_1(k8_funct_2(A, B, C, D, E)) & v1_funct_2(k8_funct_2(A, B, C, D, E), A, C)) & m1_subset_1(k8_funct_2(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 4.86/1.92  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.86/1.92  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.86/1.92  tff(f_171, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 4.86/1.92  tff(f_147, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.86/1.92  tff(c_76, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.86/1.92  tff(c_60, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.86/1.92  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.86/1.92  tff(c_207, plain, (![C_124, A_125, B_126]: (~v1_partfun1(C_124, A_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_xboole_0(B_126) | v1_xboole_0(A_125))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.86/1.92  tff(c_210, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_207])).
% 4.86/1.92  tff(c_222, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_210])).
% 4.86/1.92  tff(c_223, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_76, c_222])).
% 4.86/1.92  tff(c_62, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.86/1.92  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.86/1.92  tff(c_114, plain, (![C_90, A_91, B_92]: (v1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.86/1.92  tff(c_126, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_114])).
% 4.86/1.92  tff(c_140, plain, (![C_98, B_99, A_100]: (v5_relat_1(C_98, B_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.86/1.92  tff(c_154, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_140])).
% 4.86/1.92  tff(c_14, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.86/1.92  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.86/1.92  tff(c_235, plain, (![C_129, A_130, B_131]: (v1_funct_2(C_129, A_130, B_131) | ~v1_partfun1(C_129, A_130) | ~v1_funct_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.86/1.92  tff(c_238, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_235])).
% 4.86/1.92  tff(c_250, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_60, c_238])).
% 4.86/1.92  tff(c_256, plain, (![B_136, A_137, C_138]: (k1_xboole_0=B_136 | k1_relset_1(A_137, B_136, C_138)=A_137 | ~v1_funct_2(C_138, A_137, B_136) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.86/1.92  tff(c_259, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_256])).
% 4.86/1.92  tff(c_271, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_259])).
% 4.86/1.92  tff(c_294, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_271])).
% 4.86/1.92  tff(c_74, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.86/1.92  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.86/1.92  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.86/1.92  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.86/1.92  tff(c_390, plain, (![D_162, B_163, C_166, A_165, E_164]: (v1_funct_2(k8_funct_2(A_165, B_163, C_166, D_162, E_164), A_165, C_166) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(B_163, C_166))) | ~v1_funct_1(E_164) | ~m1_subset_1(D_162, k1_zfmisc_1(k2_zfmisc_1(A_165, B_163))) | ~v1_funct_2(D_162, A_165, B_163) | ~v1_funct_1(D_162))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.86/1.92  tff(c_521, plain, (![A_191, A_192, D_193, E_194]: (v1_funct_2(k8_funct_2(A_191, A_192, k1_xboole_0, D_193, E_194), A_191, k1_xboole_0) | ~m1_subset_1(E_194, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(E_194) | ~m1_subset_1(D_193, k1_zfmisc_1(k2_zfmisc_1(A_191, A_192))) | ~v1_funct_2(D_193, A_191, A_192) | ~v1_funct_1(D_193))), inference(superposition, [status(thm), theory('equality')], [c_6, c_390])).
% 4.86/1.92  tff(c_527, plain, (![E_194]: (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', k1_xboole_0, '#skF_4', E_194), '#skF_2', k1_xboole_0) | ~m1_subset_1(E_194, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(E_194) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_521])).
% 4.86/1.92  tff(c_543, plain, (![E_196]: (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', k1_xboole_0, '#skF_4', E_196), '#skF_2', k1_xboole_0) | ~m1_subset_1(E_196, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(E_196))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_527])).
% 4.86/1.92  tff(c_38, plain, (![C_30, A_28]: (k1_xboole_0=C_30 | ~v1_funct_2(C_30, A_28, k1_xboole_0) | k1_xboole_0=A_28 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.86/1.92  tff(c_80, plain, (![C_30, A_28]: (k1_xboole_0=C_30 | ~v1_funct_2(C_30, A_28, k1_xboole_0) | k1_xboole_0=A_28 | ~m1_subset_1(C_30, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_38])).
% 4.86/1.92  tff(c_546, plain, (![E_196]: (k8_funct_2('#skF_2', '#skF_1', k1_xboole_0, '#skF_4', E_196)=k1_xboole_0 | k1_xboole_0='#skF_2' | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', k1_xboole_0, '#skF_4', E_196), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(E_196, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(E_196))), inference(resolution, [status(thm)], [c_543, c_80])).
% 4.86/1.92  tff(c_604, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_546])).
% 4.86/1.92  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.86/1.92  tff(c_637, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_604, c_2])).
% 4.86/1.92  tff(c_639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_637])).
% 4.86/1.92  tff(c_641, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_546])).
% 4.86/1.92  tff(c_180, plain, (![A_113, B_114, C_115]: (k2_relset_1(A_113, B_114, C_115)=k2_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.86/1.92  tff(c_194, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_180])).
% 4.86/1.92  tff(c_583, plain, (![A_200, F_202, B_203, E_199, D_198, C_201]: (k1_funct_1(k8_funct_2(B_203, C_201, A_200, D_198, E_199), F_202)=k1_funct_1(E_199, k1_funct_1(D_198, F_202)) | k1_xboole_0=B_203 | ~r1_tarski(k2_relset_1(B_203, C_201, D_198), k1_relset_1(C_201, A_200, E_199)) | ~m1_subset_1(F_202, B_203) | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(C_201, A_200))) | ~v1_funct_1(E_199) | ~m1_subset_1(D_198, k1_zfmisc_1(k2_zfmisc_1(B_203, C_201))) | ~v1_funct_2(D_198, B_203, C_201) | ~v1_funct_1(D_198) | v1_xboole_0(C_201))), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.86/1.92  tff(c_589, plain, (![A_200, E_199, F_202]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_200, '#skF_4', E_199), F_202)=k1_funct_1(E_199, k1_funct_1('#skF_4', F_202)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_200, E_199)) | ~m1_subset_1(F_202, '#skF_2') | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_200))) | ~v1_funct_1(E_199) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_194, c_583])).
% 4.86/1.92  tff(c_599, plain, (![A_200, E_199, F_202]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_200, '#skF_4', E_199), F_202)=k1_funct_1(E_199, k1_funct_1('#skF_4', F_202)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_200, E_199)) | ~m1_subset_1(F_202, '#skF_2') | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_200))) | ~v1_funct_1(E_199) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_589])).
% 4.86/1.92  tff(c_600, plain, (![A_200, E_199, F_202]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_200, '#skF_4', E_199), F_202)=k1_funct_1(E_199, k1_funct_1('#skF_4', F_202)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_200, E_199)) | ~m1_subset_1(F_202, '#skF_2') | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_200))) | ~v1_funct_1(E_199))), inference(negUnitSimplification, [status(thm)], [c_76, c_599])).
% 4.86/1.92  tff(c_643, plain, (![A_204, E_205, F_206]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_204, '#skF_4', E_205), F_206)=k1_funct_1(E_205, k1_funct_1('#skF_4', F_206)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_204, E_205)) | ~m1_subset_1(F_206, '#skF_2') | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_204))) | ~v1_funct_1(E_205))), inference(negUnitSimplification, [status(thm)], [c_641, c_600])).
% 4.86/1.92  tff(c_645, plain, (![F_206]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_206)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_206)) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_206, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_294, c_643])).
% 4.86/1.92  tff(c_650, plain, (![F_206]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_206)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_206)) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_206, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_645])).
% 4.86/1.92  tff(c_654, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_650])).
% 4.86/1.92  tff(c_657, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_654])).
% 4.86/1.92  tff(c_661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_154, c_657])).
% 4.86/1.92  tff(c_662, plain, (![F_206]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_206)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_206)) | ~m1_subset_1(F_206, '#skF_2'))), inference(splitRight, [status(thm)], [c_650])).
% 4.86/1.92  tff(c_350, plain, (![C_155, B_152, A_154, D_151, E_153]: (v1_funct_1(k8_funct_2(A_154, B_152, C_155, D_151, E_153)) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(B_152, C_155))) | ~v1_funct_1(E_153) | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(A_154, B_152))) | ~v1_funct_2(D_151, A_154, B_152) | ~v1_funct_1(D_151))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.86/1.92  tff(c_352, plain, (![A_154, D_151]: (v1_funct_1(k8_funct_2(A_154, '#skF_1', '#skF_3', D_151, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(A_154, '#skF_1'))) | ~v1_funct_2(D_151, A_154, '#skF_1') | ~v1_funct_1(D_151))), inference(resolution, [status(thm)], [c_64, c_350])).
% 4.86/1.92  tff(c_379, plain, (![A_160, D_161]: (v1_funct_1(k8_funct_2(A_160, '#skF_1', '#skF_3', D_161, '#skF_5')) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(A_160, '#skF_1'))) | ~v1_funct_2(D_161, A_160, '#skF_1') | ~v1_funct_1(D_161))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_352])).
% 4.86/1.92  tff(c_382, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_379])).
% 4.86/1.92  tff(c_389, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_382])).
% 4.86/1.92  tff(c_392, plain, (![A_165, D_162]: (v1_funct_2(k8_funct_2(A_165, '#skF_1', '#skF_3', D_162, '#skF_5'), A_165, '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_162, k1_zfmisc_1(k2_zfmisc_1(A_165, '#skF_1'))) | ~v1_funct_2(D_162, A_165, '#skF_1') | ~v1_funct_1(D_162))), inference(resolution, [status(thm)], [c_64, c_390])).
% 4.86/1.92  tff(c_416, plain, (![A_171, D_172]: (v1_funct_2(k8_funct_2(A_171, '#skF_1', '#skF_3', D_172, '#skF_5'), A_171, '#skF_3') | ~m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(A_171, '#skF_1'))) | ~v1_funct_2(D_172, A_171, '#skF_1') | ~v1_funct_1(D_172))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_392])).
% 4.86/1.92  tff(c_418, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_416])).
% 4.86/1.92  tff(c_424, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_418])).
% 4.86/1.92  tff(c_430, plain, (![C_182, A_181, B_179, D_178, E_180]: (m1_subset_1(k8_funct_2(A_181, B_179, C_182, D_178, E_180), k1_zfmisc_1(k2_zfmisc_1(A_181, C_182))) | ~m1_subset_1(E_180, k1_zfmisc_1(k2_zfmisc_1(B_179, C_182))) | ~v1_funct_1(E_180) | ~m1_subset_1(D_178, k1_zfmisc_1(k2_zfmisc_1(A_181, B_179))) | ~v1_funct_2(D_178, A_181, B_179) | ~v1_funct_1(D_178))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.86/1.92  tff(c_327, plain, (![A_145, B_146, C_147, D_148]: (k3_funct_2(A_145, B_146, C_147, D_148)=k1_funct_1(C_147, D_148) | ~m1_subset_1(D_148, A_145) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~v1_funct_2(C_147, A_145, B_146) | ~v1_funct_1(C_147) | v1_xboole_0(A_145))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.86/1.92  tff(c_333, plain, (![B_146, C_147]: (k3_funct_2('#skF_2', B_146, C_147, '#skF_6')=k1_funct_1(C_147, '#skF_6') | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_146))) | ~v1_funct_2(C_147, '#skF_2', B_146) | ~v1_funct_1(C_147) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_62, c_327])).
% 4.86/1.92  tff(c_338, plain, (![B_146, C_147]: (k3_funct_2('#skF_2', B_146, C_147, '#skF_6')=k1_funct_1(C_147, '#skF_6') | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_146))) | ~v1_funct_2(C_147, '#skF_2', B_146) | ~v1_funct_1(C_147))), inference(negUnitSimplification, [status(thm)], [c_74, c_333])).
% 4.86/1.92  tff(c_1271, plain, (![C_383, B_384, D_385, E_386]: (k3_funct_2('#skF_2', C_383, k8_funct_2('#skF_2', B_384, C_383, D_385, E_386), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', B_384, C_383, D_385, E_386), '#skF_6') | ~v1_funct_2(k8_funct_2('#skF_2', B_384, C_383, D_385, E_386), '#skF_2', C_383) | ~v1_funct_1(k8_funct_2('#skF_2', B_384, C_383, D_385, E_386)) | ~m1_subset_1(E_386, k1_zfmisc_1(k2_zfmisc_1(B_384, C_383))) | ~v1_funct_1(E_386) | ~m1_subset_1(D_385, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_384))) | ~v1_funct_2(D_385, '#skF_2', B_384) | ~v1_funct_1(D_385))), inference(resolution, [status(thm)], [c_430, c_338])).
% 4.86/1.92  tff(c_1278, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_424, c_1271])).
% 4.86/1.92  tff(c_1286, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_389, c_1278])).
% 4.86/1.92  tff(c_339, plain, (![B_149, C_150]: (k3_funct_2('#skF_2', B_149, C_150, '#skF_6')=k1_funct_1(C_150, '#skF_6') | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_149))) | ~v1_funct_2(C_150, '#skF_2', B_149) | ~v1_funct_1(C_150))), inference(negUnitSimplification, [status(thm)], [c_74, c_333])).
% 4.86/1.92  tff(c_342, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_339])).
% 4.86/1.92  tff(c_349, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_342])).
% 4.86/1.92  tff(c_58, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.86/1.92  tff(c_366, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_349, c_58])).
% 4.86/1.92  tff(c_1287, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1286, c_366])).
% 4.86/1.92  tff(c_1294, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_662, c_1287])).
% 4.86/1.92  tff(c_1298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_1294])).
% 4.86/1.92  tff(c_1299, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_271])).
% 4.86/1.92  tff(c_1319, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_2])).
% 4.86/1.92  tff(c_1321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_223, c_1319])).
% 4.86/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.86/1.92  
% 4.86/1.92  Inference rules
% 4.86/1.92  ----------------------
% 4.86/1.92  #Ref     : 0
% 4.86/1.92  #Sup     : 265
% 4.86/1.92  #Fact    : 0
% 4.86/1.92  #Define  : 0
% 4.86/1.92  #Split   : 11
% 4.86/1.92  #Chain   : 0
% 4.86/1.92  #Close   : 0
% 4.86/1.92  
% 4.86/1.92  Ordering : KBO
% 4.86/1.92  
% 4.86/1.92  Simplification rules
% 4.86/1.92  ----------------------
% 4.86/1.92  #Subsume      : 31
% 4.86/1.92  #Demod        : 323
% 4.86/1.92  #Tautology    : 38
% 4.86/1.92  #SimpNegUnit  : 15
% 4.86/1.92  #BackRed      : 84
% 4.86/1.92  
% 4.86/1.92  #Partial instantiations: 0
% 4.86/1.92  #Strategies tried      : 1
% 4.86/1.92  
% 4.86/1.93  Timing (in seconds)
% 4.86/1.93  ----------------------
% 4.86/1.93  Preprocessing        : 0.39
% 4.86/1.93  Parsing              : 0.21
% 4.86/1.93  CNF conversion       : 0.03
% 4.86/1.93  Main loop            : 0.70
% 4.86/1.93  Inferencing          : 0.23
% 4.86/1.93  Reduction            : 0.23
% 4.86/1.93  Demodulation         : 0.16
% 4.86/1.93  BG Simplification    : 0.03
% 4.86/1.93  Subsumption          : 0.17
% 4.86/1.93  Abstraction          : 0.03
% 4.86/1.93  MUC search           : 0.00
% 4.86/1.93  Cooper               : 0.00
% 4.86/1.93  Total                : 1.14
% 4.86/1.93  Index Insertion      : 0.00
% 4.86/1.93  Index Deletion       : 0.00
% 4.86/1.93  Index Matching       : 0.00
% 4.86/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
