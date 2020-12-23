%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:56 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 836 expanded)
%              Number of leaves         :   29 ( 264 expanded)
%              Depth                    :   13
%              Number of atoms          :  167 (2813 expanded)
%              Number of equality atoms :   32 ( 954 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_69,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_108,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( r2_relset_1(A_51,B_52,C_53,C_53)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_122,plain,(
    ! [C_57] :
      ( r2_relset_1('#skF_2','#skF_3',C_57,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_40,c_108])).

tff(c_127,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_122])).

tff(c_30,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_45,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_42,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_131,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_partfun1(C_59,A_60)
      | ~ v1_funct_2(C_59,A_60,B_61)
      | ~ v1_funct_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | v1_xboole_0(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_134,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_131])).

tff(c_146,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_134])).

tff(c_157,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_69,plain,(
    ! [B_35,A_36] :
      ( ~ v1_xboole_0(B_35)
      | B_35 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_72,plain,(
    ! [A_36] :
      ( k1_xboole_0 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_2,c_69])).

tff(c_160,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_157,c_72])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_160])).

tff(c_167,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_168,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_36,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_137,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_131])).

tff(c_149,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_137])).

tff(c_169,plain,(
    v1_partfun1('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_149])).

tff(c_32,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_151,plain,(
    ! [D_62,C_63,A_64,B_65] :
      ( D_62 = C_63
      | ~ r1_partfun1(C_63,D_62)
      | ~ v1_partfun1(D_62,A_64)
      | ~ v1_partfun1(C_63,A_64)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_1(D_62)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_153,plain,(
    ! [A_64,B_65] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_64)
      | ~ v1_partfun1('#skF_4',A_64)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_151])).

tff(c_156,plain,(
    ! [A_64,B_65] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_64)
      | ~ v1_partfun1('#skF_4',A_64)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_153])).

tff(c_171,plain,(
    ! [A_66,B_67] :
      ( ~ v1_partfun1('#skF_5',A_66)
      | ~ v1_partfun1('#skF_4',A_66)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_174,plain,
    ( ~ v1_partfun1('#skF_5','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_34,c_171])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_167,c_169,c_174])).

tff(c_185,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_28,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_189,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_28])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_189])).

tff(c_200,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_16,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_1'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_255,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_1'(A_12),A_12)
      | A_12 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_16])).

tff(c_199,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_206,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_199])).

tff(c_201,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_2])).

tff(c_211,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_201])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_218,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_8])).

tff(c_254,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_206,c_40])).

tff(c_269,plain,(
    ! [C_76,B_77,A_78] :
      ( ~ v1_xboole_0(C_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(C_76))
      | ~ r2_hidden(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_271,plain,(
    ! [A_78] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_78,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_254,c_269])).

tff(c_280,plain,(
    ! [A_79] : ~ r2_hidden(A_79,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_271])).

tff(c_285,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_255,c_280])).

tff(c_288,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_254])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_226,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_10])).

tff(c_292,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_285,c_226])).

tff(c_416,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( r2_relset_1(A_105,B_106,C_107,C_107)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_418,plain,(
    ! [B_4,C_107,D_108] :
      ( r2_relset_1('#skF_4',B_4,C_107,C_107)
      | ~ m1_subset_1(D_108,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_4))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_416])).

tff(c_421,plain,(
    ! [B_4,C_107,D_108] :
      ( r2_relset_1('#skF_4',B_4,C_107,C_107)
      | ~ m1_subset_1(D_108,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_107,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_418])).

tff(c_430,plain,(
    ! [D_108] : ~ m1_subset_1(D_108,k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_430,c_288])).

tff(c_434,plain,(
    ! [B_113,C_114] :
      ( r2_relset_1('#skF_4',B_113,C_114,C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_437,plain,(
    ! [B_113] : r2_relset_1('#skF_4',B_113,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_288,c_434])).

tff(c_357,plain,(
    ! [A_90] :
      ( r2_hidden('#skF_1'(A_90),A_90)
      | A_90 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_255])).

tff(c_243,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_206,c_34])).

tff(c_273,plain,(
    ! [A_78] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_78,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_243,c_269])).

tff(c_279,plain,(
    ! [A_78] : ~ r2_hidden(A_78,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_273])).

tff(c_369,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_357,c_279])).

tff(c_242,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_28])).

tff(c_291,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_285,c_242])).

tff(c_372,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_291])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.32  
% 2.14/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.32  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.14/1.32  
% 2.14/1.32  %Foreground sorts:
% 2.14/1.32  
% 2.14/1.32  
% 2.14/1.32  %Background operators:
% 2.14/1.32  
% 2.14/1.32  
% 2.14/1.32  %Foreground operators:
% 2.14/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.14/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.32  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.14/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.14/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.14/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.14/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.14/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.32  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.14/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.32  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.14/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.32  
% 2.53/1.34  tff(f_123, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 2.53/1.34  tff(f_53, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.53/1.34  tff(f_83, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.53/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.53/1.34  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.53/1.34  tff(f_100, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.53/1.34  tff(f_69, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.53/1.34  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.53/1.34  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.53/1.34  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.53/1.34  tff(c_108, plain, (![A_51, B_52, C_53, D_54]: (r2_relset_1(A_51, B_52, C_53, C_53) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.34  tff(c_122, plain, (![C_57]: (r2_relset_1('#skF_2', '#skF_3', C_57, C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_40, c_108])).
% 2.53/1.34  tff(c_127, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_122])).
% 2.53/1.34  tff(c_30, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.53/1.34  tff(c_45, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_30])).
% 2.53/1.34  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.53/1.34  tff(c_42, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.53/1.34  tff(c_131, plain, (![C_59, A_60, B_61]: (v1_partfun1(C_59, A_60) | ~v1_funct_2(C_59, A_60, B_61) | ~v1_funct_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | v1_xboole_0(B_61))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.53/1.34  tff(c_134, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_131])).
% 2.53/1.34  tff(c_146, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_134])).
% 2.53/1.34  tff(c_157, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_146])).
% 2.53/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.53/1.34  tff(c_69, plain, (![B_35, A_36]: (~v1_xboole_0(B_35) | B_35=A_36 | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.53/1.34  tff(c_72, plain, (![A_36]: (k1_xboole_0=A_36 | ~v1_xboole_0(A_36))), inference(resolution, [status(thm)], [c_2, c_69])).
% 2.53/1.34  tff(c_160, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_157, c_72])).
% 2.53/1.34  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_160])).
% 2.53/1.34  tff(c_167, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_146])).
% 2.53/1.34  tff(c_168, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_146])).
% 2.53/1.34  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.53/1.34  tff(c_36, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.53/1.34  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.53/1.34  tff(c_137, plain, (v1_partfun1('#skF_5', '#skF_2') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_131])).
% 2.53/1.34  tff(c_149, plain, (v1_partfun1('#skF_5', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_137])).
% 2.53/1.34  tff(c_169, plain, (v1_partfun1('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_168, c_149])).
% 2.53/1.34  tff(c_32, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.53/1.34  tff(c_151, plain, (![D_62, C_63, A_64, B_65]: (D_62=C_63 | ~r1_partfun1(C_63, D_62) | ~v1_partfun1(D_62, A_64) | ~v1_partfun1(C_63, A_64) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_1(D_62) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_1(C_63))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.53/1.34  tff(c_153, plain, (![A_64, B_65]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_64) | ~v1_partfun1('#skF_4', A_64) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_151])).
% 2.53/1.34  tff(c_156, plain, (![A_64, B_65]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_64) | ~v1_partfun1('#skF_4', A_64) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_153])).
% 2.53/1.34  tff(c_171, plain, (![A_66, B_67]: (~v1_partfun1('#skF_5', A_66) | ~v1_partfun1('#skF_4', A_66) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(splitLeft, [status(thm)], [c_156])).
% 2.53/1.34  tff(c_174, plain, (~v1_partfun1('#skF_5', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_34, c_171])).
% 2.53/1.34  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_167, c_169, c_174])).
% 2.53/1.34  tff(c_185, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_156])).
% 2.53/1.34  tff(c_28, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.53/1.34  tff(c_189, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_28])).
% 2.53/1.34  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_189])).
% 2.53/1.34  tff(c_200, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.53/1.34  tff(c_16, plain, (![A_12]: (r2_hidden('#skF_1'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.53/1.34  tff(c_255, plain, (![A_12]: (r2_hidden('#skF_1'(A_12), A_12) | A_12='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_16])).
% 2.53/1.34  tff(c_199, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 2.53/1.34  tff(c_206, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_199])).
% 2.53/1.34  tff(c_201, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_2])).
% 2.53/1.34  tff(c_211, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_201])).
% 2.53/1.34  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.53/1.34  tff(c_218, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_8])).
% 2.53/1.34  tff(c_254, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_206, c_40])).
% 2.53/1.34  tff(c_269, plain, (![C_76, B_77, A_78]: (~v1_xboole_0(C_76) | ~m1_subset_1(B_77, k1_zfmisc_1(C_76)) | ~r2_hidden(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.53/1.34  tff(c_271, plain, (![A_78]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_78, '#skF_4'))), inference(resolution, [status(thm)], [c_254, c_269])).
% 2.53/1.34  tff(c_280, plain, (![A_79]: (~r2_hidden(A_79, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_271])).
% 2.53/1.34  tff(c_285, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_255, c_280])).
% 2.53/1.34  tff(c_288, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_285, c_254])).
% 2.53/1.34  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.53/1.34  tff(c_226, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_10])).
% 2.53/1.34  tff(c_292, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_285, c_285, c_226])).
% 2.53/1.34  tff(c_416, plain, (![A_105, B_106, C_107, D_108]: (r2_relset_1(A_105, B_106, C_107, C_107) | ~m1_subset_1(D_108, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.34  tff(c_418, plain, (![B_4, C_107, D_108]: (r2_relset_1('#skF_4', B_4, C_107, C_107) | ~m1_subset_1(D_108, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_4))))), inference(superposition, [status(thm), theory('equality')], [c_292, c_416])).
% 2.53/1.34  tff(c_421, plain, (![B_4, C_107, D_108]: (r2_relset_1('#skF_4', B_4, C_107, C_107) | ~m1_subset_1(D_108, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_107, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_418])).
% 2.53/1.34  tff(c_430, plain, (![D_108]: (~m1_subset_1(D_108, k1_zfmisc_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_421])).
% 2.53/1.34  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_430, c_288])).
% 2.53/1.34  tff(c_434, plain, (![B_113, C_114]: (r2_relset_1('#skF_4', B_113, C_114, C_114) | ~m1_subset_1(C_114, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_421])).
% 2.53/1.34  tff(c_437, plain, (![B_113]: (r2_relset_1('#skF_4', B_113, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_288, c_434])).
% 2.53/1.34  tff(c_357, plain, (![A_90]: (r2_hidden('#skF_1'(A_90), A_90) | A_90='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_285, c_255])).
% 2.53/1.34  tff(c_243, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_206, c_34])).
% 2.53/1.34  tff(c_273, plain, (![A_78]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_78, '#skF_5'))), inference(resolution, [status(thm)], [c_243, c_269])).
% 2.53/1.34  tff(c_279, plain, (![A_78]: (~r2_hidden(A_78, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_273])).
% 2.53/1.34  tff(c_369, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_357, c_279])).
% 2.53/1.34  tff(c_242, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_28])).
% 2.53/1.34  tff(c_291, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_285, c_285, c_242])).
% 2.53/1.34  tff(c_372, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_369, c_291])).
% 2.53/1.34  tff(c_440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_437, c_372])).
% 2.53/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.34  
% 2.53/1.34  Inference rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Ref     : 0
% 2.53/1.34  #Sup     : 80
% 2.53/1.34  #Fact    : 0
% 2.53/1.34  #Define  : 0
% 2.53/1.34  #Split   : 7
% 2.53/1.34  #Chain   : 0
% 2.53/1.34  #Close   : 0
% 2.53/1.34  
% 2.53/1.34  Ordering : KBO
% 2.53/1.34  
% 2.53/1.34  Simplification rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Subsume      : 10
% 2.53/1.34  #Demod        : 85
% 2.53/1.34  #Tautology    : 52
% 2.53/1.34  #SimpNegUnit  : 3
% 2.53/1.34  #BackRed      : 33
% 2.53/1.34  
% 2.53/1.34  #Partial instantiations: 0
% 2.53/1.34  #Strategies tried      : 1
% 2.53/1.34  
% 2.53/1.34  Timing (in seconds)
% 2.53/1.34  ----------------------
% 2.53/1.34  Preprocessing        : 0.30
% 2.53/1.34  Parsing              : 0.16
% 2.53/1.34  CNF conversion       : 0.02
% 2.53/1.34  Main loop            : 0.25
% 2.53/1.34  Inferencing          : 0.09
% 2.53/1.34  Reduction            : 0.08
% 2.53/1.34  Demodulation         : 0.06
% 2.53/1.34  BG Simplification    : 0.02
% 2.53/1.34  Subsumption          : 0.04
% 2.53/1.34  Abstraction          : 0.01
% 2.53/1.34  MUC search           : 0.00
% 2.53/1.34  Cooper               : 0.00
% 2.53/1.34  Total                : 0.60
% 2.53/1.34  Index Insertion      : 0.00
% 2.53/1.34  Index Deletion       : 0.00
% 2.53/1.34  Index Matching       : 0.00
% 2.53/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
