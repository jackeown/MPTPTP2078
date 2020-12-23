%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:46 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :  275 (15572 expanded)
%              Number of leaves         :   39 (5028 expanded)
%              Depth                    :   19
%              Number of atoms          :  431 (36599 expanded)
%              Number of equality atoms :  141 (5181 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
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

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_6684,plain,(
    ! [C_618,A_619,B_620] :
      ( v1_relat_1(C_618)
      | ~ m1_subset_1(C_618,k1_zfmisc_1(k2_zfmisc_1(A_619,B_620))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6701,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_6684])).

tff(c_76,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_70,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_68,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_8008,plain,(
    ! [A_735,B_736,C_737] :
      ( k2_relset_1(A_735,B_736,C_737) = k2_relat_1(C_737)
      | ~ m1_subset_1(C_737,k1_zfmisc_1(k2_zfmisc_1(A_735,B_736))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_8021,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_8008])).

tff(c_8032,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_8021])).

tff(c_38,plain,(
    ! [A_18] :
      ( k1_relat_1(k2_funct_1(A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2361,plain,(
    ! [A_268,B_269,C_270] :
      ( k2_relset_1(A_268,B_269,C_270) = k2_relat_1(C_270)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2371,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_2361])).

tff(c_2381,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2371])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [A_17] :
      ( v1_funct_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_140,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_143,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_140])).

tff(c_146,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_143])).

tff(c_165,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_172,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_165])).

tff(c_181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_172])).

tff(c_182,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_193,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_197,plain,(
    ~ r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_193])).

tff(c_217,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_230,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_217])).

tff(c_74,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2215,plain,(
    ! [A_254,B_255,C_256] :
      ( k1_relset_1(A_254,B_255,C_256) = k1_relat_1(C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2234,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_2215])).

tff(c_2525,plain,(
    ! [B_285,A_286,C_287] :
      ( k1_xboole_0 = B_285
      | k1_relset_1(A_286,B_285,C_287) = A_286
      | ~ v1_funct_2(C_287,A_286,B_285)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_286,B_285))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2538,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_2525])).

tff(c_2552,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2234,c_2538])).

tff(c_2554,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2552])).

tff(c_36,plain,(
    ! [A_18] :
      ( k2_relat_1(k2_funct_1(A_18)) = k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2076,plain,(
    ! [A_237] :
      ( k1_relat_1(k2_funct_1(A_237)) = k2_relat_1(A_237)
      | ~ v2_funct_1(A_237)
      | ~ v1_funct_1(A_237)
      | ~ v1_relat_1(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    ! [A_16] :
      ( r1_tarski(A_16,k2_zfmisc_1(k1_relat_1(A_16),k2_relat_1(A_16)))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3872,plain,(
    ! [A_387] :
      ( r1_tarski(k2_funct_1(A_387),k2_zfmisc_1(k2_relat_1(A_387),k2_relat_1(k2_funct_1(A_387))))
      | ~ v1_relat_1(k2_funct_1(A_387))
      | ~ v2_funct_1(A_387)
      | ~ v1_funct_1(A_387)
      | ~ v1_relat_1(A_387) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2076,c_26])).

tff(c_3901,plain,
    ( r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2381,c_3872])).

tff(c_3922,plain,
    ( r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_76,c_70,c_3901])).

tff(c_3926,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3922])).

tff(c_3963,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_3926])).

tff(c_3967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_76,c_3963])).

tff(c_3968,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_3922])).

tff(c_3998,plain,
    ( r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_3968])).

tff(c_4015,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_76,c_70,c_2554,c_3998])).

tff(c_4017,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_4015])).

tff(c_4018,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2552])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4049,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4018,c_12])).

tff(c_18,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4046,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4018,c_4018,c_18])).

tff(c_2396,plain,
    ( r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2381,c_26])).

tff(c_2408,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_2396])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_309,plain,(
    ! [C_77,B_78,A_79] :
      ( r2_hidden(C_77,B_78)
      | ~ r2_hidden(C_77,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_329,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_1'(A_84),B_85)
      | ~ r1_tarski(A_84,B_85)
      | v1_xboole_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_4,c_309])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_340,plain,(
    ! [B_85,A_84] :
      ( ~ v1_xboole_0(B_85)
      | ~ r1_tarski(A_84,B_85)
      | v1_xboole_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_329,c_2])).

tff(c_2419,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2408,c_340])).

tff(c_2458,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2419])).

tff(c_4205,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4046,c_2458])).

tff(c_4213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4049,c_4205])).

tff(c_4214,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_2419])).

tff(c_116,plain,(
    ! [B_38,A_39] :
      ( ~ v1_xboole_0(B_38)
      | B_38 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_119,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_12,c_116])).

tff(c_4234,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4214,c_119])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4256,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4234,c_4234,c_28])).

tff(c_4261,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2381,c_4256])).

tff(c_4268,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4261,c_4214])).

tff(c_4255,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4234,c_4234,c_18])).

tff(c_4433,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4261,c_4261,c_4255])).

tff(c_184,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_192,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_72,c_184])).

tff(c_341,plain,(
    ! [B_86,A_87] :
      ( ~ v1_xboole_0(B_86)
      | ~ r1_tarski(A_87,B_86)
      | v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_329,c_2])).

tff(c_357,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_192,c_341])).

tff(c_358,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_4434,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4433,c_358])).

tff(c_4437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4268,c_4434])).

tff(c_4439,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_4438,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( ~ v1_xboole_0(B_11)
      | B_11 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4571,plain,(
    ! [A_404] :
      ( A_404 = '#skF_5'
      | ~ v1_xboole_0(A_404) ) ),
    inference(resolution,[status(thm)],[c_4438,c_14])).

tff(c_4578,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4439,c_4571])).

tff(c_4450,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4438,c_119])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k2_zfmisc_1(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4678,plain,(
    ! [B_411,A_412] :
      ( B_411 = '#skF_5'
      | A_412 = '#skF_5'
      | k2_zfmisc_1(A_412,B_411) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4450,c_4450,c_4450,c_16])).

tff(c_4690,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4578,c_4678])).

tff(c_4693,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4690])).

tff(c_4713,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4693,c_68])).

tff(c_4459,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4450,c_4450,c_28])).

tff(c_4705,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4693,c_4693,c_4459])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_274,plain,(
    ! [A_73,B_74] :
      ( ~ r2_hidden('#skF_2'(A_73,B_74),B_74)
      | r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_279,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_274])).

tff(c_48,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_30,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_79,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_48])).

tff(c_4468,plain,(
    ! [A_30] :
      ( v1_funct_2('#skF_5',A_30,'#skF_5')
      | A_30 = '#skF_5'
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4450,c_4450,c_4450,c_4450,c_4450,c_79])).

tff(c_4469,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4468])).

tff(c_4508,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_4469])).

tff(c_4512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_4508])).

tff(c_4514,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4468])).

tff(c_4703,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4693,c_4693,c_4514])).

tff(c_4700,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4693,c_4578])).

tff(c_46,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_relset_1(A_27,B_28,C_29) = k2_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4947,plain,(
    ! [C_430] :
      ( k2_relset_1('#skF_3','#skF_4',C_430) = k2_relat_1(C_430)
      | ~ m1_subset_1(C_430,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4700,c_46])).

tff(c_4950,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4703,c_4947])).

tff(c_4956,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4713,c_4705,c_4950])).

tff(c_4708,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4693,c_230])).

tff(c_4981,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4956,c_4708])).

tff(c_4716,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4693,c_76])).

tff(c_4979,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4956,c_4716])).

tff(c_4458,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4450,c_4450,c_18])).

tff(c_4702,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4693,c_4693,c_4458])).

tff(c_4711,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4693,c_193])).

tff(c_4885,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4702,c_4711])).

tff(c_4889,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_4885])).

tff(c_4961,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4956,c_4956,c_4889])).

tff(c_4715,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4693,c_70])).

tff(c_4980,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4956,c_4715])).

tff(c_4967,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4956,c_4956,c_4702])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4460,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4450,c_4450,c_30])).

tff(c_4704,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4693,c_4693,c_4460])).

tff(c_4974,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4956,c_4956,c_4704])).

tff(c_4663,plain,(
    ! [A_410] :
      ( k2_relat_1(k2_funct_1(A_410)) = k1_relat_1(A_410)
      | ~ v2_funct_1(A_410)
      | ~ v1_funct_1(A_410)
      | ~ v1_relat_1(A_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5743,plain,(
    ! [A_515] :
      ( r1_tarski(k2_funct_1(A_515),k2_zfmisc_1(k1_relat_1(k2_funct_1(A_515)),k1_relat_1(A_515)))
      | ~ v1_relat_1(k2_funct_1(A_515))
      | ~ v2_funct_1(A_515)
      | ~ v1_funct_1(A_515)
      | ~ v1_relat_1(A_515) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4663,c_26])).

tff(c_5760,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4974,c_5743])).

tff(c_5773,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4981,c_4979,c_4980,c_4967,c_5760])).

tff(c_5774,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_4961,c_5773])).

tff(c_5777,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_5774])).

tff(c_5781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4981,c_4979,c_5777])).

tff(c_5782,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4690])).

tff(c_5798,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5782,c_230])).

tff(c_5806,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5782,c_76])).

tff(c_20,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4457,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_5',B_13) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4450,c_4450,c_20])).

tff(c_5789,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5782,c_5782,c_4457])).

tff(c_5801,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5782,c_193])).

tff(c_5988,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_5801])).

tff(c_5992,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_5988])).

tff(c_5805,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5782,c_70])).

tff(c_5792,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5782,c_5782,c_4458])).

tff(c_5794,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5782,c_5782,c_4460])).

tff(c_6635,plain,(
    ! [A_615] :
      ( r1_tarski(k2_funct_1(A_615),k2_zfmisc_1(k1_relat_1(k2_funct_1(A_615)),k1_relat_1(A_615)))
      | ~ v1_relat_1(k2_funct_1(A_615))
      | ~ v2_funct_1(A_615)
      | ~ v1_funct_1(A_615)
      | ~ v1_relat_1(A_615) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4663,c_26])).

tff(c_6654,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5794,c_6635])).

tff(c_6668,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5798,c_5806,c_5805,c_5792,c_6654])).

tff(c_6669,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_5992,c_6668])).

tff(c_6672,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_6669])).

tff(c_6676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5798,c_5806,c_6672])).

tff(c_6677,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_6678,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_7902,plain,(
    ! [A_728,B_729,C_730] :
      ( k1_relset_1(A_728,B_729,C_730) = k1_relat_1(C_730)
      | ~ m1_subset_1(C_730,k1_zfmisc_1(k2_zfmisc_1(A_728,B_729))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_7923,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6678,c_7902])).

tff(c_8349,plain,(
    ! [B_767,C_768,A_769] :
      ( k1_xboole_0 = B_767
      | v1_funct_2(C_768,A_769,B_767)
      | k1_relset_1(A_769,B_767,C_768) != A_769
      | ~ m1_subset_1(C_768,k1_zfmisc_1(k2_zfmisc_1(A_769,B_767))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8355,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_6678,c_8349])).

tff(c_8371,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7923,c_8355])).

tff(c_8372,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_6677,c_8371])).

tff(c_8378,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8372])).

tff(c_8381,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_8378])).

tff(c_8384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6701,c_76,c_70,c_8032,c_8381])).

tff(c_8385,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8372])).

tff(c_8419,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8385,c_12])).

tff(c_8415,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_3',B_13) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8385,c_8385,c_20])).

tff(c_6789,plain,(
    ! [C_636,B_637,A_638] :
      ( r2_hidden(C_636,B_637)
      | ~ r2_hidden(C_636,A_638)
      | ~ r1_tarski(A_638,B_637) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6817,plain,(
    ! [A_642,B_643] :
      ( r2_hidden('#skF_1'(A_642),B_643)
      | ~ r1_tarski(A_642,B_643)
      | v1_xboole_0(A_642) ) ),
    inference(resolution,[status(thm)],[c_4,c_6789])).

tff(c_7733,plain,(
    ! [B_709,A_710] :
      ( ~ v1_xboole_0(B_709)
      | ~ r1_tarski(A_710,B_709)
      | v1_xboole_0(A_710) ) ),
    inference(resolution,[status(thm)],[c_6817,c_2])).

tff(c_7753,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_192,c_7733])).

tff(c_7754,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7753])).

tff(c_8565,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8415,c_7754])).

tff(c_8570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8419,c_8565])).

tff(c_8572,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7753])).

tff(c_8571,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_7753])).

tff(c_8753,plain,(
    ! [A_776] :
      ( A_776 = '#skF_5'
      | ~ v1_xboole_0(A_776) ) ),
    inference(resolution,[status(thm)],[c_8571,c_14])).

tff(c_8760,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8572,c_8753])).

tff(c_8583,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8571,c_119])).

tff(c_8869,plain,(
    ! [B_786,A_787] :
      ( B_786 = '#skF_5'
      | A_787 = '#skF_5'
      | k2_zfmisc_1(A_787,B_786) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8583,c_8583,c_8583,c_16])).

tff(c_8879,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_8760,c_8869])).

tff(c_8884,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8879])).

tff(c_8919,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8884,c_8571])).

tff(c_8593,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8583,c_8583,c_18])).

tff(c_8912,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8884,c_8884,c_8593])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6682,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6678,c_22])).

tff(c_7752,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3'))
    | v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6682,c_7733])).

tff(c_8868,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7752])).

tff(c_9030,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8912,c_8868])).

tff(c_9033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8919,c_9030])).

tff(c_9034,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8879])).

tff(c_9051,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9034,c_8571])).

tff(c_8592,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_5',B_13) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8583,c_8583,c_20])).

tff(c_9046,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9034,c_9034,c_8592])).

tff(c_9151,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9046,c_8868])).

tff(c_9154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9051,c_9151])).

tff(c_9156,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7752])).

tff(c_8584,plain,(
    ! [A_10] :
      ( A_10 = '#skF_5'
      | ~ v1_xboole_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_8571,c_14])).

tff(c_9212,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_9156,c_8584])).

tff(c_9258,plain,(
    ! [B_800,A_801] :
      ( B_800 = '#skF_5'
      | A_801 = '#skF_5'
      | k2_zfmisc_1(A_801,B_800) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8583,c_8583,c_8583,c_16])).

tff(c_9271,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_9212,c_9258])).

tff(c_9277,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9271])).

tff(c_8595,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8583,c_8583,c_30])).

tff(c_9155,plain,(
    v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_7752])).

tff(c_9165,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_9155,c_8584])).

tff(c_8844,plain,(
    ! [A_783,B_784,C_785] :
      ( k1_relset_1(A_783,B_784,C_785) = k1_relat_1(C_785)
      | ~ m1_subset_1(C_785,k1_zfmisc_1(k2_zfmisc_1(A_783,B_784))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8861,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6678,c_8844])).

tff(c_9170,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9165,c_9165,c_8861])).

tff(c_9177,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8595,c_9170])).

tff(c_9279,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9277,c_9277,c_9177])).

tff(c_6708,plain,(
    ! [A_622,B_623] :
      ( r2_hidden('#skF_2'(A_622,B_623),A_622)
      | r1_tarski(A_622,B_623) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6719,plain,(
    ! [A_622] : r1_tarski(A_622,A_622) ),
    inference(resolution,[status(thm)],[c_6708,c_8])).

tff(c_8618,plain,(
    ! [A_30] :
      ( v1_funct_2('#skF_5',A_30,'#skF_5')
      | A_30 = '#skF_5'
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8583,c_8583,c_8583,c_8583,c_8583,c_79])).

tff(c_8619,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8618])).

tff(c_8690,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_8619])).

tff(c_8694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6719,c_8690])).

tff(c_8696,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_8618])).

tff(c_9292,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9277,c_9277,c_8696])).

tff(c_9295,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9277,c_8583])).

tff(c_52,plain,(
    ! [C_32,B_31] :
      ( v1_funct_2(C_32,k1_xboole_0,B_31)
      | k1_relset_1(k1_xboole_0,B_31,C_32) != k1_xboole_0
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_78,plain,(
    ! [C_32,B_31] :
      ( v1_funct_2(C_32,k1_xboole_0,B_31)
      | k1_relset_1(k1_xboole_0,B_31,C_32) != k1_xboole_0
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_52])).

tff(c_9404,plain,(
    ! [C_32,B_31] :
      ( v1_funct_2(C_32,'#skF_4',B_31)
      | k1_relset_1('#skF_4',B_31,C_32) != '#skF_4'
      | ~ m1_subset_1(C_32,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9295,c_9295,c_9295,c_9295,c_78])).

tff(c_9688,plain,(
    ! [B_837] :
      ( v1_funct_2('#skF_4','#skF_4',B_837)
      | k1_relset_1('#skF_4',B_837,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_9292,c_9404])).

tff(c_9174,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9165,c_6677])).

tff(c_9281,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9277,c_9174])).

tff(c_9693,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_9688,c_9281])).

tff(c_9700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9279,c_9693])).

tff(c_9701,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9271])).

tff(c_9702,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9271])).

tff(c_9732,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9701,c_9702])).

tff(c_8695,plain,(
    ! [A_30] :
      ( v1_funct_2('#skF_5',A_30,'#skF_5')
      | A_30 = '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_8618])).

tff(c_9958,plain,(
    ! [A_850] :
      ( v1_funct_2('#skF_3',A_850,'#skF_3')
      | A_850 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9701,c_9701,c_9701,c_8695])).

tff(c_9707,plain,(
    ~ v1_funct_2('#skF_3','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9701,c_9174])).

tff(c_9961,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9958,c_9707])).

tff(c_9968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9732,c_9961])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:08:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.69/2.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.69/2.71  
% 7.69/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.69/2.71  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 7.69/2.71  
% 7.69/2.71  %Foreground sorts:
% 7.69/2.71  
% 7.69/2.71  
% 7.69/2.71  %Background operators:
% 7.69/2.71  
% 7.69/2.71  
% 7.69/2.71  %Foreground operators:
% 7.69/2.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.69/2.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.69/2.71  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.69/2.71  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.69/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.69/2.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.69/2.71  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.69/2.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.69/2.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.69/2.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.69/2.71  tff('#skF_5', type, '#skF_5': $i).
% 7.69/2.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.69/2.71  tff('#skF_3', type, '#skF_3': $i).
% 7.69/2.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.69/2.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.69/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.69/2.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.69/2.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.69/2.71  tff('#skF_4', type, '#skF_4': $i).
% 7.69/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.69/2.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.69/2.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.69/2.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.69/2.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.69/2.71  
% 7.94/2.74  tff(f_144, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 7.94/2.74  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.94/2.74  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.94/2.74  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.94/2.74  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.94/2.74  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.94/2.74  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.94/2.74  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.94/2.74  tff(f_61, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 7.94/2.74  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.94/2.74  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.94/2.74  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.94/2.74  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.94/2.74  tff(f_47, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 7.94/2.74  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 7.94/2.74  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.94/2.74  tff(c_6684, plain, (![C_618, A_619, B_620]: (v1_relat_1(C_618) | ~m1_subset_1(C_618, k1_zfmisc_1(k2_zfmisc_1(A_619, B_620))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.94/2.74  tff(c_6701, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_6684])).
% 7.94/2.74  tff(c_76, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.94/2.74  tff(c_70, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.94/2.74  tff(c_68, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.94/2.74  tff(c_8008, plain, (![A_735, B_736, C_737]: (k2_relset_1(A_735, B_736, C_737)=k2_relat_1(C_737) | ~m1_subset_1(C_737, k1_zfmisc_1(k2_zfmisc_1(A_735, B_736))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.94/2.74  tff(c_8021, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_8008])).
% 7.94/2.74  tff(c_8032, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_8021])).
% 7.94/2.74  tff(c_38, plain, (![A_18]: (k1_relat_1(k2_funct_1(A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.94/2.74  tff(c_2361, plain, (![A_268, B_269, C_270]: (k2_relset_1(A_268, B_269, C_270)=k2_relat_1(C_270) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.94/2.74  tff(c_2371, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_2361])).
% 7.94/2.74  tff(c_2381, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2371])).
% 7.94/2.74  tff(c_24, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.94/2.74  tff(c_32, plain, (![A_17]: (v1_funct_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.94/2.74  tff(c_66, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.94/2.74  tff(c_140, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_66])).
% 7.94/2.74  tff(c_143, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_140])).
% 7.94/2.74  tff(c_146, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_143])).
% 7.94/2.74  tff(c_165, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.94/2.74  tff(c_172, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_165])).
% 7.94/2.74  tff(c_181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_172])).
% 7.94/2.74  tff(c_182, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_66])).
% 7.94/2.74  tff(c_193, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_182])).
% 7.94/2.74  tff(c_197, plain, (~r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_193])).
% 7.94/2.74  tff(c_217, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.94/2.74  tff(c_230, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_217])).
% 7.94/2.74  tff(c_74, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.94/2.74  tff(c_2215, plain, (![A_254, B_255, C_256]: (k1_relset_1(A_254, B_255, C_256)=k1_relat_1(C_256) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.94/2.74  tff(c_2234, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_2215])).
% 7.94/2.74  tff(c_2525, plain, (![B_285, A_286, C_287]: (k1_xboole_0=B_285 | k1_relset_1(A_286, B_285, C_287)=A_286 | ~v1_funct_2(C_287, A_286, B_285) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(A_286, B_285))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.94/2.74  tff(c_2538, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_2525])).
% 7.94/2.74  tff(c_2552, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2234, c_2538])).
% 7.94/2.74  tff(c_2554, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_2552])).
% 7.94/2.74  tff(c_36, plain, (![A_18]: (k2_relat_1(k2_funct_1(A_18))=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.94/2.74  tff(c_34, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.94/2.74  tff(c_2076, plain, (![A_237]: (k1_relat_1(k2_funct_1(A_237))=k2_relat_1(A_237) | ~v2_funct_1(A_237) | ~v1_funct_1(A_237) | ~v1_relat_1(A_237))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.94/2.74  tff(c_26, plain, (![A_16]: (r1_tarski(A_16, k2_zfmisc_1(k1_relat_1(A_16), k2_relat_1(A_16))) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.94/2.74  tff(c_3872, plain, (![A_387]: (r1_tarski(k2_funct_1(A_387), k2_zfmisc_1(k2_relat_1(A_387), k2_relat_1(k2_funct_1(A_387)))) | ~v1_relat_1(k2_funct_1(A_387)) | ~v2_funct_1(A_387) | ~v1_funct_1(A_387) | ~v1_relat_1(A_387))), inference(superposition, [status(thm), theory('equality')], [c_2076, c_26])).
% 7.94/2.74  tff(c_3901, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2381, c_3872])).
% 7.94/2.74  tff(c_3922, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_76, c_70, c_3901])).
% 7.94/2.74  tff(c_3926, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_3922])).
% 7.94/2.74  tff(c_3963, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_3926])).
% 7.94/2.74  tff(c_3967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_230, c_76, c_3963])).
% 7.94/2.74  tff(c_3968, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))), inference(splitRight, [status(thm)], [c_3922])).
% 7.94/2.74  tff(c_3998, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_36, c_3968])).
% 7.94/2.74  tff(c_4015, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_76, c_70, c_2554, c_3998])).
% 7.94/2.74  tff(c_4017, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_4015])).
% 7.94/2.74  tff(c_4018, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2552])).
% 7.94/2.74  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.94/2.74  tff(c_4049, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4018, c_12])).
% 7.94/2.74  tff(c_18, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.94/2.74  tff(c_4046, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4018, c_4018, c_18])).
% 7.94/2.74  tff(c_2396, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2381, c_26])).
% 7.94/2.74  tff(c_2408, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_2396])).
% 7.94/2.74  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.94/2.74  tff(c_309, plain, (![C_77, B_78, A_79]: (r2_hidden(C_77, B_78) | ~r2_hidden(C_77, A_79) | ~r1_tarski(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.94/2.74  tff(c_329, plain, (![A_84, B_85]: (r2_hidden('#skF_1'(A_84), B_85) | ~r1_tarski(A_84, B_85) | v1_xboole_0(A_84))), inference(resolution, [status(thm)], [c_4, c_309])).
% 7.94/2.74  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.94/2.74  tff(c_340, plain, (![B_85, A_84]: (~v1_xboole_0(B_85) | ~r1_tarski(A_84, B_85) | v1_xboole_0(A_84))), inference(resolution, [status(thm)], [c_329, c_2])).
% 7.94/2.74  tff(c_2419, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_2408, c_340])).
% 7.94/2.74  tff(c_2458, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_2419])).
% 7.94/2.74  tff(c_4205, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4046, c_2458])).
% 7.94/2.74  tff(c_4213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4049, c_4205])).
% 7.94/2.74  tff(c_4214, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_2419])).
% 7.94/2.74  tff(c_116, plain, (![B_38, A_39]: (~v1_xboole_0(B_38) | B_38=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.94/2.74  tff(c_119, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_12, c_116])).
% 7.94/2.74  tff(c_4234, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_4214, c_119])).
% 7.94/2.74  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.94/2.74  tff(c_4256, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4234, c_4234, c_28])).
% 7.94/2.74  tff(c_4261, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2381, c_4256])).
% 7.94/2.74  tff(c_4268, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4261, c_4214])).
% 7.94/2.74  tff(c_4255, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4234, c_4234, c_18])).
% 7.94/2.74  tff(c_4433, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4261, c_4261, c_4255])).
% 7.94/2.74  tff(c_184, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.94/2.74  tff(c_192, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_184])).
% 7.94/2.74  tff(c_341, plain, (![B_86, A_87]: (~v1_xboole_0(B_86) | ~r1_tarski(A_87, B_86) | v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_329, c_2])).
% 7.94/2.74  tff(c_357, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_192, c_341])).
% 7.94/2.74  tff(c_358, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_357])).
% 7.94/2.74  tff(c_4434, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4433, c_358])).
% 7.94/2.74  tff(c_4437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4268, c_4434])).
% 7.94/2.74  tff(c_4439, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_357])).
% 7.94/2.74  tff(c_4438, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_357])).
% 7.94/2.74  tff(c_14, plain, (![B_11, A_10]: (~v1_xboole_0(B_11) | B_11=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.94/2.74  tff(c_4571, plain, (![A_404]: (A_404='#skF_5' | ~v1_xboole_0(A_404))), inference(resolution, [status(thm)], [c_4438, c_14])).
% 7.94/2.74  tff(c_4578, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_4439, c_4571])).
% 7.94/2.74  tff(c_4450, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_4438, c_119])).
% 7.94/2.74  tff(c_16, plain, (![B_13, A_12]: (k1_xboole_0=B_13 | k1_xboole_0=A_12 | k2_zfmisc_1(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.94/2.74  tff(c_4678, plain, (![B_411, A_412]: (B_411='#skF_5' | A_412='#skF_5' | k2_zfmisc_1(A_412, B_411)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4450, c_4450, c_4450, c_16])).
% 7.94/2.74  tff(c_4690, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4578, c_4678])).
% 7.94/2.74  tff(c_4693, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_4690])).
% 7.94/2.74  tff(c_4713, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4693, c_68])).
% 7.94/2.74  tff(c_4459, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4450, c_4450, c_28])).
% 7.94/2.74  tff(c_4705, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4693, c_4693, c_4459])).
% 7.94/2.74  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.94/2.74  tff(c_274, plain, (![A_73, B_74]: (~r2_hidden('#skF_2'(A_73, B_74), B_74) | r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.94/2.74  tff(c_279, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_274])).
% 7.94/2.74  tff(c_48, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_30, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.94/2.74  tff(c_79, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_48])).
% 7.94/2.74  tff(c_4468, plain, (![A_30]: (v1_funct_2('#skF_5', A_30, '#skF_5') | A_30='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_4450, c_4450, c_4450, c_4450, c_4450, c_79])).
% 7.94/2.74  tff(c_4469, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_4468])).
% 7.94/2.74  tff(c_4508, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_4469])).
% 7.94/2.74  tff(c_4512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_279, c_4508])).
% 7.94/2.74  tff(c_4514, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_4468])).
% 7.94/2.74  tff(c_4703, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4693, c_4693, c_4514])).
% 7.94/2.74  tff(c_4700, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4693, c_4578])).
% 7.94/2.74  tff(c_46, plain, (![A_27, B_28, C_29]: (k2_relset_1(A_27, B_28, C_29)=k2_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.94/2.74  tff(c_4947, plain, (![C_430]: (k2_relset_1('#skF_3', '#skF_4', C_430)=k2_relat_1(C_430) | ~m1_subset_1(C_430, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4700, c_46])).
% 7.94/2.74  tff(c_4950, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4703, c_4947])).
% 7.94/2.74  tff(c_4956, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4713, c_4705, c_4950])).
% 7.94/2.74  tff(c_4708, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4693, c_230])).
% 7.94/2.74  tff(c_4981, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4956, c_4708])).
% 7.94/2.74  tff(c_4716, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4693, c_76])).
% 7.94/2.74  tff(c_4979, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4956, c_4716])).
% 7.94/2.74  tff(c_4458, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4450, c_4450, c_18])).
% 7.94/2.74  tff(c_4702, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4693, c_4693, c_4458])).
% 7.94/2.74  tff(c_4711, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4693, c_193])).
% 7.94/2.74  tff(c_4885, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4702, c_4711])).
% 7.94/2.74  tff(c_4889, plain, (~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_24, c_4885])).
% 7.94/2.74  tff(c_4961, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4956, c_4956, c_4889])).
% 7.94/2.74  tff(c_4715, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4693, c_70])).
% 7.94/2.74  tff(c_4980, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4956, c_4715])).
% 7.94/2.74  tff(c_4967, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4956, c_4956, c_4702])).
% 7.94/2.74  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.94/2.74  tff(c_4460, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4450, c_4450, c_30])).
% 7.94/2.74  tff(c_4704, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4693, c_4693, c_4460])).
% 7.94/2.74  tff(c_4974, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4956, c_4956, c_4704])).
% 7.94/2.74  tff(c_4663, plain, (![A_410]: (k2_relat_1(k2_funct_1(A_410))=k1_relat_1(A_410) | ~v2_funct_1(A_410) | ~v1_funct_1(A_410) | ~v1_relat_1(A_410))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.94/2.74  tff(c_5743, plain, (![A_515]: (r1_tarski(k2_funct_1(A_515), k2_zfmisc_1(k1_relat_1(k2_funct_1(A_515)), k1_relat_1(A_515))) | ~v1_relat_1(k2_funct_1(A_515)) | ~v2_funct_1(A_515) | ~v1_funct_1(A_515) | ~v1_relat_1(A_515))), inference(superposition, [status(thm), theory('equality')], [c_4663, c_26])).
% 7.94/2.74  tff(c_5760, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4974, c_5743])).
% 7.94/2.74  tff(c_5773, plain, (r1_tarski(k2_funct_1('#skF_4'), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4981, c_4979, c_4980, c_4967, c_5760])).
% 7.94/2.74  tff(c_5774, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_4961, c_5773])).
% 7.94/2.74  tff(c_5777, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_5774])).
% 7.94/2.74  tff(c_5781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4981, c_4979, c_5777])).
% 7.94/2.74  tff(c_5782, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_4690])).
% 7.94/2.74  tff(c_5798, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5782, c_230])).
% 7.94/2.74  tff(c_5806, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5782, c_76])).
% 7.94/2.74  tff(c_20, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.94/2.74  tff(c_4457, plain, (![B_13]: (k2_zfmisc_1('#skF_5', B_13)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4450, c_4450, c_20])).
% 7.94/2.74  tff(c_5789, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5782, c_5782, c_4457])).
% 7.94/2.74  tff(c_5801, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5782, c_193])).
% 7.94/2.74  tff(c_5988, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_5801])).
% 7.94/2.74  tff(c_5992, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_24, c_5988])).
% 7.94/2.74  tff(c_5805, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5782, c_70])).
% 7.94/2.74  tff(c_5792, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5782, c_5782, c_4458])).
% 7.94/2.74  tff(c_5794, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5782, c_5782, c_4460])).
% 7.94/2.74  tff(c_6635, plain, (![A_615]: (r1_tarski(k2_funct_1(A_615), k2_zfmisc_1(k1_relat_1(k2_funct_1(A_615)), k1_relat_1(A_615))) | ~v1_relat_1(k2_funct_1(A_615)) | ~v2_funct_1(A_615) | ~v1_funct_1(A_615) | ~v1_relat_1(A_615))), inference(superposition, [status(thm), theory('equality')], [c_4663, c_26])).
% 7.94/2.74  tff(c_6654, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5794, c_6635])).
% 7.94/2.74  tff(c_6668, plain, (r1_tarski(k2_funct_1('#skF_4'), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5798, c_5806, c_5805, c_5792, c_6654])).
% 7.94/2.74  tff(c_6669, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_5992, c_6668])).
% 7.94/2.74  tff(c_6672, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_6669])).
% 7.94/2.74  tff(c_6676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5798, c_5806, c_6672])).
% 7.94/2.74  tff(c_6677, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_182])).
% 7.94/2.74  tff(c_6678, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_182])).
% 7.94/2.74  tff(c_7902, plain, (![A_728, B_729, C_730]: (k1_relset_1(A_728, B_729, C_730)=k1_relat_1(C_730) | ~m1_subset_1(C_730, k1_zfmisc_1(k2_zfmisc_1(A_728, B_729))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.94/2.74  tff(c_7923, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_6678, c_7902])).
% 7.94/2.74  tff(c_8349, plain, (![B_767, C_768, A_769]: (k1_xboole_0=B_767 | v1_funct_2(C_768, A_769, B_767) | k1_relset_1(A_769, B_767, C_768)!=A_769 | ~m1_subset_1(C_768, k1_zfmisc_1(k2_zfmisc_1(A_769, B_767))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.94/2.74  tff(c_8355, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_6678, c_8349])).
% 7.94/2.74  tff(c_8371, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7923, c_8355])).
% 7.94/2.74  tff(c_8372, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_6677, c_8371])).
% 7.94/2.74  tff(c_8378, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_8372])).
% 7.94/2.74  tff(c_8381, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_38, c_8378])).
% 7.94/2.74  tff(c_8384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6701, c_76, c_70, c_8032, c_8381])).
% 7.94/2.74  tff(c_8385, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_8372])).
% 7.94/2.74  tff(c_8419, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8385, c_12])).
% 7.94/2.74  tff(c_8415, plain, (![B_13]: (k2_zfmisc_1('#skF_3', B_13)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8385, c_8385, c_20])).
% 7.94/2.74  tff(c_6789, plain, (![C_636, B_637, A_638]: (r2_hidden(C_636, B_637) | ~r2_hidden(C_636, A_638) | ~r1_tarski(A_638, B_637))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.94/2.74  tff(c_6817, plain, (![A_642, B_643]: (r2_hidden('#skF_1'(A_642), B_643) | ~r1_tarski(A_642, B_643) | v1_xboole_0(A_642))), inference(resolution, [status(thm)], [c_4, c_6789])).
% 7.94/2.74  tff(c_7733, plain, (![B_709, A_710]: (~v1_xboole_0(B_709) | ~r1_tarski(A_710, B_709) | v1_xboole_0(A_710))), inference(resolution, [status(thm)], [c_6817, c_2])).
% 7.94/2.74  tff(c_7753, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_192, c_7733])).
% 7.94/2.74  tff(c_7754, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_7753])).
% 7.94/2.74  tff(c_8565, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8415, c_7754])).
% 7.94/2.74  tff(c_8570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8419, c_8565])).
% 7.94/2.74  tff(c_8572, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_7753])).
% 7.94/2.74  tff(c_8571, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_7753])).
% 7.94/2.74  tff(c_8753, plain, (![A_776]: (A_776='#skF_5' | ~v1_xboole_0(A_776))), inference(resolution, [status(thm)], [c_8571, c_14])).
% 7.94/2.74  tff(c_8760, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_8572, c_8753])).
% 7.94/2.74  tff(c_8583, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_8571, c_119])).
% 7.94/2.74  tff(c_8869, plain, (![B_786, A_787]: (B_786='#skF_5' | A_787='#skF_5' | k2_zfmisc_1(A_787, B_786)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8583, c_8583, c_8583, c_16])).
% 7.94/2.74  tff(c_8879, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_8760, c_8869])).
% 7.94/2.74  tff(c_8884, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_8879])).
% 7.94/2.74  tff(c_8919, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8884, c_8571])).
% 7.94/2.74  tff(c_8593, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8583, c_8583, c_18])).
% 7.94/2.74  tff(c_8912, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8884, c_8884, c_8593])).
% 7.94/2.74  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.94/2.74  tff(c_6682, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_6678, c_22])).
% 7.94/2.74  tff(c_7752, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3')) | v1_xboole_0(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_6682, c_7733])).
% 7.94/2.74  tff(c_8868, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_7752])).
% 7.94/2.74  tff(c_9030, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8912, c_8868])).
% 7.94/2.74  tff(c_9033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8919, c_9030])).
% 7.94/2.74  tff(c_9034, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_8879])).
% 7.94/2.74  tff(c_9051, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9034, c_8571])).
% 7.94/2.74  tff(c_8592, plain, (![B_13]: (k2_zfmisc_1('#skF_5', B_13)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8583, c_8583, c_20])).
% 7.94/2.74  tff(c_9046, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9034, c_9034, c_8592])).
% 7.94/2.74  tff(c_9151, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9046, c_8868])).
% 7.94/2.74  tff(c_9154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9051, c_9151])).
% 7.94/2.74  tff(c_9156, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_7752])).
% 7.94/2.74  tff(c_8584, plain, (![A_10]: (A_10='#skF_5' | ~v1_xboole_0(A_10))), inference(resolution, [status(thm)], [c_8571, c_14])).
% 7.94/2.74  tff(c_9212, plain, (k2_zfmisc_1('#skF_4', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_9156, c_8584])).
% 7.94/2.74  tff(c_9258, plain, (![B_800, A_801]: (B_800='#skF_5' | A_801='#skF_5' | k2_zfmisc_1(A_801, B_800)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8583, c_8583, c_8583, c_16])).
% 7.94/2.74  tff(c_9271, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_9212, c_9258])).
% 7.94/2.74  tff(c_9277, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_9271])).
% 7.94/2.74  tff(c_8595, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8583, c_8583, c_30])).
% 7.94/2.74  tff(c_9155, plain, (v1_xboole_0(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_7752])).
% 7.94/2.74  tff(c_9165, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_9155, c_8584])).
% 7.94/2.74  tff(c_8844, plain, (![A_783, B_784, C_785]: (k1_relset_1(A_783, B_784, C_785)=k1_relat_1(C_785) | ~m1_subset_1(C_785, k1_zfmisc_1(k2_zfmisc_1(A_783, B_784))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.94/2.74  tff(c_8861, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_6678, c_8844])).
% 7.94/2.74  tff(c_9170, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9165, c_9165, c_8861])).
% 7.94/2.74  tff(c_9177, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8595, c_9170])).
% 7.94/2.74  tff(c_9279, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9277, c_9277, c_9177])).
% 7.94/2.74  tff(c_6708, plain, (![A_622, B_623]: (r2_hidden('#skF_2'(A_622, B_623), A_622) | r1_tarski(A_622, B_623))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.94/2.74  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.94/2.74  tff(c_6719, plain, (![A_622]: (r1_tarski(A_622, A_622))), inference(resolution, [status(thm)], [c_6708, c_8])).
% 7.94/2.74  tff(c_8618, plain, (![A_30]: (v1_funct_2('#skF_5', A_30, '#skF_5') | A_30='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8583, c_8583, c_8583, c_8583, c_8583, c_79])).
% 7.94/2.74  tff(c_8619, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_8618])).
% 7.94/2.74  tff(c_8690, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_8619])).
% 7.94/2.74  tff(c_8694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6719, c_8690])).
% 7.94/2.74  tff(c_8696, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_8618])).
% 7.94/2.74  tff(c_9292, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9277, c_9277, c_8696])).
% 7.94/2.74  tff(c_9295, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9277, c_8583])).
% 7.94/2.74  tff(c_52, plain, (![C_32, B_31]: (v1_funct_2(C_32, k1_xboole_0, B_31) | k1_relset_1(k1_xboole_0, B_31, C_32)!=k1_xboole_0 | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_31))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.94/2.74  tff(c_78, plain, (![C_32, B_31]: (v1_funct_2(C_32, k1_xboole_0, B_31) | k1_relset_1(k1_xboole_0, B_31, C_32)!=k1_xboole_0 | ~m1_subset_1(C_32, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_52])).
% 7.94/2.74  tff(c_9404, plain, (![C_32, B_31]: (v1_funct_2(C_32, '#skF_4', B_31) | k1_relset_1('#skF_4', B_31, C_32)!='#skF_4' | ~m1_subset_1(C_32, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9295, c_9295, c_9295, c_9295, c_78])).
% 7.94/2.74  tff(c_9688, plain, (![B_837]: (v1_funct_2('#skF_4', '#skF_4', B_837) | k1_relset_1('#skF_4', B_837, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_9292, c_9404])).
% 7.94/2.74  tff(c_9174, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9165, c_6677])).
% 7.94/2.74  tff(c_9281, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9277, c_9174])).
% 7.94/2.74  tff(c_9693, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_9688, c_9281])).
% 7.94/2.74  tff(c_9700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9279, c_9693])).
% 7.94/2.74  tff(c_9701, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_9271])).
% 7.94/2.74  tff(c_9702, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_9271])).
% 7.94/2.74  tff(c_9732, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9701, c_9702])).
% 7.94/2.74  tff(c_8695, plain, (![A_30]: (v1_funct_2('#skF_5', A_30, '#skF_5') | A_30='#skF_5')), inference(splitRight, [status(thm)], [c_8618])).
% 7.94/2.74  tff(c_9958, plain, (![A_850]: (v1_funct_2('#skF_3', A_850, '#skF_3') | A_850='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9701, c_9701, c_9701, c_8695])).
% 7.94/2.74  tff(c_9707, plain, (~v1_funct_2('#skF_3', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9701, c_9174])).
% 7.94/2.74  tff(c_9961, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_9958, c_9707])).
% 7.94/2.74  tff(c_9968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9732, c_9961])).
% 7.94/2.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.94/2.74  
% 7.94/2.74  Inference rules
% 7.94/2.74  ----------------------
% 7.94/2.74  #Ref     : 0
% 7.94/2.74  #Sup     : 2133
% 7.94/2.74  #Fact    : 0
% 7.94/2.74  #Define  : 0
% 7.94/2.74  #Split   : 39
% 7.94/2.74  #Chain   : 0
% 7.94/2.74  #Close   : 0
% 7.94/2.74  
% 7.94/2.74  Ordering : KBO
% 7.94/2.74  
% 7.94/2.74  Simplification rules
% 7.94/2.74  ----------------------
% 7.94/2.74  #Subsume      : 324
% 7.94/2.74  #Demod        : 2596
% 7.94/2.74  #Tautology    : 1147
% 7.94/2.74  #SimpNegUnit  : 19
% 7.94/2.74  #BackRed      : 527
% 7.94/2.74  
% 7.94/2.74  #Partial instantiations: 0
% 7.94/2.74  #Strategies tried      : 1
% 7.94/2.74  
% 7.94/2.74  Timing (in seconds)
% 7.94/2.74  ----------------------
% 7.94/2.75  Preprocessing        : 0.37
% 7.94/2.75  Parsing              : 0.19
% 7.94/2.75  CNF conversion       : 0.02
% 7.94/2.75  Main loop            : 1.55
% 7.94/2.75  Inferencing          : 0.54
% 7.94/2.75  Reduction            : 0.53
% 7.94/2.75  Demodulation         : 0.37
% 7.94/2.75  BG Simplification    : 0.06
% 7.94/2.75  Subsumption          : 0.29
% 7.94/2.75  Abstraction          : 0.06
% 7.94/2.75  MUC search           : 0.00
% 7.94/2.75  Cooper               : 0.00
% 7.94/2.75  Total                : 2.00
% 7.94/2.75  Index Insertion      : 0.00
% 7.94/2.75  Index Deletion       : 0.00
% 7.94/2.75  Index Matching       : 0.00
% 7.94/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
