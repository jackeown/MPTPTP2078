%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:11 EST 2020

% Result     : Theorem 9.66s
% Output     : CNFRefutation 9.95s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 261 expanded)
%              Number of leaves         :   37 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  194 ( 553 expanded)
%              Number of equality atoms :   28 (  78 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_15618,plain,(
    ! [A_893,B_894,C_895] :
      ( k1_relset_1(A_893,B_894,C_895) = k1_relat_1(C_895)
      | ~ m1_subset_1(C_895,k1_zfmisc_1(k2_zfmisc_1(A_893,B_894))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_15632,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_15618])).

tff(c_48,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_15633,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15632,c_48])).

tff(c_239,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_relset_1(A_103,B_104,C_105) = k2_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_253,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_239])).

tff(c_24,plain,(
    ! [A_18] :
      ( v1_xboole_0(k1_relat_1(A_18))
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_58,plain,(
    ! [A_57] :
      ( v1_xboole_0(k1_relat_1(A_57))
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ! [A_60] :
      ( k1_relat_1(A_60) = k1_xboole_0
      | ~ v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_58,c_6])).

tff(c_80,plain,(
    ! [A_65] :
      ( k1_relat_1(k1_relat_1(A_65)) = k1_xboole_0
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_24,c_64])).

tff(c_89,plain,(
    ! [A_65] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_65))
      | ~ v1_xboole_0(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_24])).

tff(c_99,plain,(
    ! [A_66] :
      ( ~ v1_xboole_0(k1_relat_1(A_66))
      | ~ v1_xboole_0(A_66) ) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_106,plain,(
    ! [A_18] : ~ v1_xboole_0(A_18) ),
    inference(resolution,[status(thm)],[c_24,c_99])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_4])).

tff(c_126,plain,(
    ! [D_72] :
      ( ~ r2_hidden(D_72,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_72,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_131,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_118,c_126])).

tff(c_259,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_131])).

tff(c_107,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_116,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_107])).

tff(c_34,plain,(
    ! [A_25] :
      ( k9_relat_1(A_25,k1_relat_1(A_25)) = k2_relat_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_541,plain,(
    ! [A_136,B_137,C_138] :
      ( r2_hidden(k4_tarski('#skF_2'(A_136,B_137,C_138),A_136),C_138)
      | ~ r2_hidden(A_136,k9_relat_1(C_138,B_137))
      | ~ v1_relat_1(C_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [C_15,A_12,B_13] :
      ( r2_hidden(C_15,A_12)
      | ~ r2_hidden(C_15,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2489,plain,(
    ! [A_275,B_276,C_277,A_278] :
      ( r2_hidden(k4_tarski('#skF_2'(A_275,B_276,C_277),A_275),A_278)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(A_278))
      | ~ r2_hidden(A_275,k9_relat_1(C_277,B_276))
      | ~ v1_relat_1(C_277) ) ),
    inference(resolution,[status(thm)],[c_541,c_20])).

tff(c_16,plain,(
    ! [B_9,D_11,A_8,C_10] :
      ( r2_hidden(B_9,D_11)
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4051,plain,(
    ! [C_357,A_356,B_354,C_355,D_358] :
      ( r2_hidden(A_356,D_358)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(C_357,D_358)))
      | ~ r2_hidden(A_356,k9_relat_1(C_355,B_354))
      | ~ v1_relat_1(C_355) ) ),
    inference(resolution,[status(thm)],[c_2489,c_16])).

tff(c_4112,plain,(
    ! [A_356,B_354] :
      ( r2_hidden(A_356,'#skF_4')
      | ~ r2_hidden(A_356,k9_relat_1('#skF_5',B_354))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_4051])).

tff(c_4150,plain,(
    ! [A_359,B_360] :
      ( r2_hidden(A_359,'#skF_4')
      | ~ r2_hidden(A_359,k9_relat_1('#skF_5',B_360)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_4112])).

tff(c_4257,plain,(
    ! [B_361] : r2_hidden('#skF_1'(k9_relat_1('#skF_5',B_361)),'#skF_4') ),
    inference(resolution,[status(thm)],[c_118,c_4150])).

tff(c_4268,plain,
    ( r2_hidden('#skF_1'(k2_relat_1('#skF_5')),'#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4257])).

tff(c_4273,plain,(
    r2_hidden('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_4268])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,B_17)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4280,plain,(
    m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4273,c_22])).

tff(c_4286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_4280])).

tff(c_4287,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4471,plain,(
    ! [A_393,B_394,C_395] :
      ( k1_relset_1(A_393,B_394,C_395) = k1_relat_1(C_395)
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1(A_393,B_394))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4485,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_4471])).

tff(c_4486,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4485,c_48])).

tff(c_4551,plain,(
    ! [A_401,B_402,C_403] :
      ( k2_relset_1(A_401,B_402,C_403) = k2_relat_1(C_403)
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(A_401,B_402))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4565,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_4551])).

tff(c_4288,plain,(
    ! [D_362] :
      ( ~ r2_hidden(D_362,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_362,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4293,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_4288])).

tff(c_4351,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4293])).

tff(c_4568,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4565,c_4351])).

tff(c_5287,plain,(
    ! [D_453,C_454,B_455,A_456] :
      ( m1_subset_1(D_453,k1_zfmisc_1(k2_zfmisc_1(C_454,B_455)))
      | ~ r1_tarski(k2_relat_1(D_453),B_455)
      | ~ m1_subset_1(D_453,k1_zfmisc_1(k2_zfmisc_1(C_454,A_456))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5398,plain,(
    ! [B_464] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_464)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_464) ) ),
    inference(resolution,[status(thm)],[c_50,c_5287])).

tff(c_38,plain,(
    ! [C_32,B_30,A_29] :
      ( v1_xboole_0(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(B_30,A_29)))
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5420,plain,(
    ! [B_464] :
      ( v1_xboole_0('#skF_5')
      | ~ v1_xboole_0(B_464)
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_464) ) ),
    inference(resolution,[status(thm)],[c_5398,c_38])).

tff(c_5424,plain,(
    ! [B_465] :
      ( ~ v1_xboole_0(B_465)
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_465) ) ),
    inference(splitLeft,[status(thm)],[c_5420])).

tff(c_5429,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_12,c_5424])).

tff(c_4317,plain,(
    ! [C_363,A_364,B_365] :
      ( v1_relat_1(C_363)
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4326,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_4317])).

tff(c_5028,plain,(
    ! [A_438,B_439,C_440] :
      ( r2_hidden(k4_tarski('#skF_2'(A_438,B_439,C_440),A_438),C_440)
      | ~ r2_hidden(A_438,k9_relat_1(C_440,B_439))
      | ~ v1_relat_1(C_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8604,plain,(
    ! [A_627,B_628,C_629,A_630] :
      ( r2_hidden(k4_tarski('#skF_2'(A_627,B_628,C_629),A_627),A_630)
      | ~ m1_subset_1(C_629,k1_zfmisc_1(A_630))
      | ~ r2_hidden(A_627,k9_relat_1(C_629,B_628))
      | ~ v1_relat_1(C_629) ) ),
    inference(resolution,[status(thm)],[c_5028,c_20])).

tff(c_15190,plain,(
    ! [D_858,B_855,C_856,A_857,C_854] :
      ( r2_hidden(A_857,D_858)
      | ~ m1_subset_1(C_854,k1_zfmisc_1(k2_zfmisc_1(C_856,D_858)))
      | ~ r2_hidden(A_857,k9_relat_1(C_854,B_855))
      | ~ v1_relat_1(C_854) ) ),
    inference(resolution,[status(thm)],[c_8604,c_16])).

tff(c_15211,plain,(
    ! [A_857,B_855] :
      ( r2_hidden(A_857,'#skF_4')
      | ~ r2_hidden(A_857,k9_relat_1('#skF_5',B_855))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_15190])).

tff(c_15223,plain,(
    ! [A_859,B_860] :
      ( r2_hidden(A_859,'#skF_4')
      | ~ r2_hidden(A_859,k9_relat_1('#skF_5',B_860)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4326,c_15211])).

tff(c_15293,plain,(
    ! [A_859] :
      ( r2_hidden(A_859,'#skF_4')
      | ~ r2_hidden(A_859,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_15223])).

tff(c_15327,plain,(
    ! [A_861] :
      ( r2_hidden(A_861,'#skF_4')
      | ~ r2_hidden(A_861,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4326,c_15293])).

tff(c_15355,plain,
    ( r2_hidden('#skF_1'(k2_relat_1('#skF_5')),'#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_15327])).

tff(c_15364,plain,(
    r2_hidden('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_5429,c_15355])).

tff(c_15371,plain,(
    m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_15364,c_22])).

tff(c_15380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4568,c_15371])).

tff(c_15381,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_5420])).

tff(c_62,plain,(
    ! [A_57] :
      ( k1_relat_1(A_57) = k1_xboole_0
      | ~ v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_58,c_6])).

tff(c_15397,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15381,c_62])).

tff(c_15411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4486,c_15397])).

tff(c_15412,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4293])).

tff(c_15421,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15412,c_6])).

tff(c_15483,plain,(
    ! [A_882,B_883,C_884] :
      ( k2_relset_1(A_882,B_883,C_884) = k2_relat_1(C_884)
      | ~ m1_subset_1(C_884,k1_zfmisc_1(k2_zfmisc_1(A_882,B_883))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_15490,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_15483])).

tff(c_15493,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15421,c_15490])).

tff(c_16451,plain,(
    ! [D_960,C_961,B_962,A_963] :
      ( m1_subset_1(D_960,k1_zfmisc_1(k2_zfmisc_1(C_961,B_962)))
      | ~ r1_tarski(k2_relat_1(D_960),B_962)
      | ~ m1_subset_1(D_960,k1_zfmisc_1(k2_zfmisc_1(C_961,A_963))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_16459,plain,(
    ! [B_962] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_962)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_962) ) ),
    inference(resolution,[status(thm)],[c_50,c_16451])).

tff(c_16495,plain,(
    ! [B_966] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_966)))
      | ~ r1_tarski(k1_xboole_0,B_966) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15493,c_16459])).

tff(c_16519,plain,(
    ! [B_966] :
      ( v1_xboole_0('#skF_5')
      | ~ v1_xboole_0(B_966)
      | ~ r1_tarski(k1_xboole_0,B_966) ) ),
    inference(resolution,[status(thm)],[c_16495,c_38])).

tff(c_16529,plain,(
    ! [B_968] :
      ( ~ v1_xboole_0(B_968)
      | ~ r1_tarski(k1_xboole_0,B_968) ) ),
    inference(splitLeft,[status(thm)],[c_16519])).

tff(c_16533,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_16529])).

tff(c_16537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4287,c_16533])).

tff(c_16538,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_16519])).

tff(c_16548,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16538,c_62])).

tff(c_16562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15633,c_16548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:36:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.66/3.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.66/3.70  
% 9.66/3.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.66/3.70  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 9.66/3.70  
% 9.66/3.70  %Foreground sorts:
% 9.66/3.70  
% 9.66/3.70  
% 9.66/3.70  %Background operators:
% 9.66/3.70  
% 9.66/3.70  
% 9.66/3.70  %Foreground operators:
% 9.66/3.70  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.66/3.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.66/3.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.66/3.70  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.66/3.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.66/3.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.66/3.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.66/3.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.66/3.70  tff('#skF_5', type, '#skF_5': $i).
% 9.66/3.70  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.66/3.70  tff('#skF_3', type, '#skF_3': $i).
% 9.66/3.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.66/3.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.66/3.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.66/3.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.66/3.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.66/3.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.66/3.70  tff('#skF_4', type, '#skF_4': $i).
% 9.66/3.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.66/3.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.66/3.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.66/3.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.66/3.70  
% 9.95/3.72  tff(f_123, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 9.95/3.72  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.95/3.72  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.95/3.72  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 9.95/3.72  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.95/3.72  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.95/3.72  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.95/3.72  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 9.95/3.72  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 9.95/3.72  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 9.95/3.72  tff(f_47, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 9.95/3.72  tff(f_58, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 9.95/3.72  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.95/3.72  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 9.95/3.72  tff(f_88, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 9.95/3.72  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.95/3.72  tff(c_15618, plain, (![A_893, B_894, C_895]: (k1_relset_1(A_893, B_894, C_895)=k1_relat_1(C_895) | ~m1_subset_1(C_895, k1_zfmisc_1(k2_zfmisc_1(A_893, B_894))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.95/3.72  tff(c_15632, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_15618])).
% 9.95/3.72  tff(c_48, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.95/3.72  tff(c_15633, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_15632, c_48])).
% 9.95/3.72  tff(c_239, plain, (![A_103, B_104, C_105]: (k2_relset_1(A_103, B_104, C_105)=k2_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.95/3.72  tff(c_253, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_239])).
% 9.95/3.72  tff(c_24, plain, (![A_18]: (v1_xboole_0(k1_relat_1(A_18)) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.95/3.72  tff(c_58, plain, (![A_57]: (v1_xboole_0(k1_relat_1(A_57)) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.95/3.72  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.95/3.72  tff(c_64, plain, (![A_60]: (k1_relat_1(A_60)=k1_xboole_0 | ~v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_58, c_6])).
% 9.95/3.72  tff(c_80, plain, (![A_65]: (k1_relat_1(k1_relat_1(A_65))=k1_xboole_0 | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_24, c_64])).
% 9.95/3.72  tff(c_89, plain, (![A_65]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_65)) | ~v1_xboole_0(A_65))), inference(superposition, [status(thm), theory('equality')], [c_80, c_24])).
% 9.95/3.72  tff(c_99, plain, (![A_66]: (~v1_xboole_0(k1_relat_1(A_66)) | ~v1_xboole_0(A_66))), inference(splitLeft, [status(thm)], [c_89])).
% 9.95/3.72  tff(c_106, plain, (![A_18]: (~v1_xboole_0(A_18))), inference(resolution, [status(thm)], [c_24, c_99])).
% 9.95/3.72  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.95/3.72  tff(c_118, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_106, c_4])).
% 9.95/3.72  tff(c_126, plain, (![D_72]: (~r2_hidden(D_72, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_72, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.95/3.72  tff(c_131, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_118, c_126])).
% 9.95/3.72  tff(c_259, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_131])).
% 9.95/3.72  tff(c_107, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.95/3.72  tff(c_116, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_107])).
% 9.95/3.72  tff(c_34, plain, (![A_25]: (k9_relat_1(A_25, k1_relat_1(A_25))=k2_relat_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.95/3.72  tff(c_541, plain, (![A_136, B_137, C_138]: (r2_hidden(k4_tarski('#skF_2'(A_136, B_137, C_138), A_136), C_138) | ~r2_hidden(A_136, k9_relat_1(C_138, B_137)) | ~v1_relat_1(C_138))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.95/3.72  tff(c_20, plain, (![C_15, A_12, B_13]: (r2_hidden(C_15, A_12) | ~r2_hidden(C_15, B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.95/3.72  tff(c_2489, plain, (![A_275, B_276, C_277, A_278]: (r2_hidden(k4_tarski('#skF_2'(A_275, B_276, C_277), A_275), A_278) | ~m1_subset_1(C_277, k1_zfmisc_1(A_278)) | ~r2_hidden(A_275, k9_relat_1(C_277, B_276)) | ~v1_relat_1(C_277))), inference(resolution, [status(thm)], [c_541, c_20])).
% 9.95/3.72  tff(c_16, plain, (![B_9, D_11, A_8, C_10]: (r2_hidden(B_9, D_11) | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.95/3.72  tff(c_4051, plain, (![C_357, A_356, B_354, C_355, D_358]: (r2_hidden(A_356, D_358) | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(C_357, D_358))) | ~r2_hidden(A_356, k9_relat_1(C_355, B_354)) | ~v1_relat_1(C_355))), inference(resolution, [status(thm)], [c_2489, c_16])).
% 9.95/3.72  tff(c_4112, plain, (![A_356, B_354]: (r2_hidden(A_356, '#skF_4') | ~r2_hidden(A_356, k9_relat_1('#skF_5', B_354)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_4051])).
% 9.95/3.72  tff(c_4150, plain, (![A_359, B_360]: (r2_hidden(A_359, '#skF_4') | ~r2_hidden(A_359, k9_relat_1('#skF_5', B_360)))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_4112])).
% 9.95/3.72  tff(c_4257, plain, (![B_361]: (r2_hidden('#skF_1'(k9_relat_1('#skF_5', B_361)), '#skF_4'))), inference(resolution, [status(thm)], [c_118, c_4150])).
% 9.95/3.72  tff(c_4268, plain, (r2_hidden('#skF_1'(k2_relat_1('#skF_5')), '#skF_4') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_34, c_4257])).
% 9.95/3.72  tff(c_4273, plain, (r2_hidden('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_4268])).
% 9.95/3.72  tff(c_22, plain, (![A_16, B_17]: (m1_subset_1(A_16, B_17) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.95/3.72  tff(c_4280, plain, (m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_4273, c_22])).
% 9.95/3.72  tff(c_4286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_259, c_4280])).
% 9.95/3.72  tff(c_4287, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_89])).
% 9.95/3.72  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.95/3.72  tff(c_4471, plain, (![A_393, B_394, C_395]: (k1_relset_1(A_393, B_394, C_395)=k1_relat_1(C_395) | ~m1_subset_1(C_395, k1_zfmisc_1(k2_zfmisc_1(A_393, B_394))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.95/3.72  tff(c_4485, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_4471])).
% 9.95/3.72  tff(c_4486, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4485, c_48])).
% 9.95/3.72  tff(c_4551, plain, (![A_401, B_402, C_403]: (k2_relset_1(A_401, B_402, C_403)=k2_relat_1(C_403) | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(A_401, B_402))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.95/3.72  tff(c_4565, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_4551])).
% 9.95/3.72  tff(c_4288, plain, (![D_362]: (~r2_hidden(D_362, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_362, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.95/3.72  tff(c_4293, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_4288])).
% 9.95/3.72  tff(c_4351, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_4293])).
% 9.95/3.72  tff(c_4568, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4565, c_4351])).
% 9.95/3.72  tff(c_5287, plain, (![D_453, C_454, B_455, A_456]: (m1_subset_1(D_453, k1_zfmisc_1(k2_zfmisc_1(C_454, B_455))) | ~r1_tarski(k2_relat_1(D_453), B_455) | ~m1_subset_1(D_453, k1_zfmisc_1(k2_zfmisc_1(C_454, A_456))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.95/3.72  tff(c_5398, plain, (![B_464]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_464))) | ~r1_tarski(k2_relat_1('#skF_5'), B_464))), inference(resolution, [status(thm)], [c_50, c_5287])).
% 9.95/3.72  tff(c_38, plain, (![C_32, B_30, A_29]: (v1_xboole_0(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(B_30, A_29))) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.95/3.72  tff(c_5420, plain, (![B_464]: (v1_xboole_0('#skF_5') | ~v1_xboole_0(B_464) | ~r1_tarski(k2_relat_1('#skF_5'), B_464))), inference(resolution, [status(thm)], [c_5398, c_38])).
% 9.95/3.72  tff(c_5424, plain, (![B_465]: (~v1_xboole_0(B_465) | ~r1_tarski(k2_relat_1('#skF_5'), B_465))), inference(splitLeft, [status(thm)], [c_5420])).
% 9.95/3.72  tff(c_5429, plain, (~v1_xboole_0(k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_5424])).
% 9.95/3.72  tff(c_4317, plain, (![C_363, A_364, B_365]: (v1_relat_1(C_363) | ~m1_subset_1(C_363, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.95/3.72  tff(c_4326, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_4317])).
% 9.95/3.72  tff(c_5028, plain, (![A_438, B_439, C_440]: (r2_hidden(k4_tarski('#skF_2'(A_438, B_439, C_440), A_438), C_440) | ~r2_hidden(A_438, k9_relat_1(C_440, B_439)) | ~v1_relat_1(C_440))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.95/3.72  tff(c_8604, plain, (![A_627, B_628, C_629, A_630]: (r2_hidden(k4_tarski('#skF_2'(A_627, B_628, C_629), A_627), A_630) | ~m1_subset_1(C_629, k1_zfmisc_1(A_630)) | ~r2_hidden(A_627, k9_relat_1(C_629, B_628)) | ~v1_relat_1(C_629))), inference(resolution, [status(thm)], [c_5028, c_20])).
% 9.95/3.72  tff(c_15190, plain, (![D_858, B_855, C_856, A_857, C_854]: (r2_hidden(A_857, D_858) | ~m1_subset_1(C_854, k1_zfmisc_1(k2_zfmisc_1(C_856, D_858))) | ~r2_hidden(A_857, k9_relat_1(C_854, B_855)) | ~v1_relat_1(C_854))), inference(resolution, [status(thm)], [c_8604, c_16])).
% 9.95/3.72  tff(c_15211, plain, (![A_857, B_855]: (r2_hidden(A_857, '#skF_4') | ~r2_hidden(A_857, k9_relat_1('#skF_5', B_855)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_15190])).
% 9.95/3.72  tff(c_15223, plain, (![A_859, B_860]: (r2_hidden(A_859, '#skF_4') | ~r2_hidden(A_859, k9_relat_1('#skF_5', B_860)))), inference(demodulation, [status(thm), theory('equality')], [c_4326, c_15211])).
% 9.95/3.72  tff(c_15293, plain, (![A_859]: (r2_hidden(A_859, '#skF_4') | ~r2_hidden(A_859, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_15223])).
% 9.95/3.72  tff(c_15327, plain, (![A_861]: (r2_hidden(A_861, '#skF_4') | ~r2_hidden(A_861, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_4326, c_15293])).
% 9.95/3.72  tff(c_15355, plain, (r2_hidden('#skF_1'(k2_relat_1('#skF_5')), '#skF_4') | v1_xboole_0(k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_15327])).
% 9.95/3.72  tff(c_15364, plain, (r2_hidden('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_5429, c_15355])).
% 9.95/3.72  tff(c_15371, plain, (m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_15364, c_22])).
% 9.95/3.72  tff(c_15380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4568, c_15371])).
% 9.95/3.72  tff(c_15381, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_5420])).
% 9.95/3.72  tff(c_62, plain, (![A_57]: (k1_relat_1(A_57)=k1_xboole_0 | ~v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_58, c_6])).
% 9.95/3.72  tff(c_15397, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_15381, c_62])).
% 9.95/3.72  tff(c_15411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4486, c_15397])).
% 9.95/3.72  tff(c_15412, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_4293])).
% 9.95/3.72  tff(c_15421, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_15412, c_6])).
% 9.95/3.72  tff(c_15483, plain, (![A_882, B_883, C_884]: (k2_relset_1(A_882, B_883, C_884)=k2_relat_1(C_884) | ~m1_subset_1(C_884, k1_zfmisc_1(k2_zfmisc_1(A_882, B_883))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.95/3.72  tff(c_15490, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_15483])).
% 9.95/3.72  tff(c_15493, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_15421, c_15490])).
% 9.95/3.72  tff(c_16451, plain, (![D_960, C_961, B_962, A_963]: (m1_subset_1(D_960, k1_zfmisc_1(k2_zfmisc_1(C_961, B_962))) | ~r1_tarski(k2_relat_1(D_960), B_962) | ~m1_subset_1(D_960, k1_zfmisc_1(k2_zfmisc_1(C_961, A_963))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.95/3.72  tff(c_16459, plain, (![B_962]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_962))) | ~r1_tarski(k2_relat_1('#skF_5'), B_962))), inference(resolution, [status(thm)], [c_50, c_16451])).
% 9.95/3.72  tff(c_16495, plain, (![B_966]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_966))) | ~r1_tarski(k1_xboole_0, B_966))), inference(demodulation, [status(thm), theory('equality')], [c_15493, c_16459])).
% 9.95/3.72  tff(c_16519, plain, (![B_966]: (v1_xboole_0('#skF_5') | ~v1_xboole_0(B_966) | ~r1_tarski(k1_xboole_0, B_966))), inference(resolution, [status(thm)], [c_16495, c_38])).
% 9.95/3.72  tff(c_16529, plain, (![B_968]: (~v1_xboole_0(B_968) | ~r1_tarski(k1_xboole_0, B_968))), inference(splitLeft, [status(thm)], [c_16519])).
% 9.95/3.72  tff(c_16533, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_16529])).
% 9.95/3.72  tff(c_16537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4287, c_16533])).
% 9.95/3.72  tff(c_16538, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_16519])).
% 9.95/3.72  tff(c_16548, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_16538, c_62])).
% 9.95/3.72  tff(c_16562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15633, c_16548])).
% 9.95/3.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.95/3.72  
% 9.95/3.72  Inference rules
% 9.95/3.72  ----------------------
% 9.95/3.72  #Ref     : 0
% 9.95/3.72  #Sup     : 3914
% 9.95/3.72  #Fact    : 0
% 9.95/3.72  #Define  : 0
% 9.95/3.72  #Split   : 24
% 9.95/3.72  #Chain   : 0
% 9.95/3.72  #Close   : 0
% 9.95/3.72  
% 9.95/3.72  Ordering : KBO
% 9.95/3.72  
% 9.95/3.72  Simplification rules
% 9.95/3.72  ----------------------
% 9.95/3.72  #Subsume      : 980
% 9.95/3.73  #Demod        : 1064
% 9.95/3.73  #Tautology    : 771
% 9.95/3.73  #SimpNegUnit  : 121
% 9.95/3.73  #BackRed      : 51
% 9.95/3.73  
% 9.95/3.73  #Partial instantiations: 0
% 9.95/3.73  #Strategies tried      : 1
% 9.95/3.73  
% 9.95/3.73  Timing (in seconds)
% 9.95/3.73  ----------------------
% 9.95/3.73  Preprocessing        : 0.33
% 9.95/3.73  Parsing              : 0.17
% 9.95/3.73  CNF conversion       : 0.02
% 9.95/3.73  Main loop            : 2.61
% 9.95/3.73  Inferencing          : 0.72
% 9.95/3.73  Reduction            : 0.68
% 9.95/3.73  Demodulation         : 0.45
% 9.95/3.73  BG Simplification    : 0.08
% 9.95/3.73  Subsumption          : 0.92
% 9.95/3.73  Abstraction          : 0.10
% 9.95/3.73  MUC search           : 0.00
% 9.95/3.73  Cooper               : 0.00
% 9.95/3.73  Total                : 2.99
% 9.95/3.73  Index Insertion      : 0.00
% 9.95/3.73  Index Deletion       : 0.00
% 9.95/3.73  Index Matching       : 0.00
% 9.95/3.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
