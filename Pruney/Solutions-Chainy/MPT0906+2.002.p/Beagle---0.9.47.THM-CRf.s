%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:54 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 338 expanded)
%              Number of leaves         :   21 ( 113 expanded)
%              Depth                    :   13
%              Number of atoms          :  122 ( 728 expanded)
%              Number of equality atoms :   51 ( 408 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) != k1_xboole_0
       => ! [C] :
            ( m1_subset_1(C,k2_zfmisc_1(A,B))
           => ( C != k1_mcart_1(C)
              & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_mcart_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ! [C] :
              ( m1_subset_1(C,k2_zfmisc_1(A,B))
             => ( C != k1_mcart_1(C)
                & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_371,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden(k1_mcart_1(A_75),B_76)
      | ~ r2_hidden(A_75,k2_zfmisc_1(B_76,C_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_562,plain,(
    ! [B_98,C_99] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_98,C_99))),B_98)
      | v1_xboole_0(k2_zfmisc_1(B_98,C_99)) ) ),
    inference(resolution,[status(thm)],[c_4,c_371])).

tff(c_83,plain,(
    ! [A_34,B_35,C_36] :
      ( r2_hidden(k1_mcart_1(A_34),B_35)
      | ~ r2_hidden(A_34,k2_zfmisc_1(B_35,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_224,plain,(
    ! [B_55,C_56] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_55,C_56))),B_55)
      | v1_xboole_0(k2_zfmisc_1(B_55,C_56)) ) ),
    inference(resolution,[status(thm)],[c_4,c_83])).

tff(c_24,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_37,plain,(
    k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_115,plain,(
    ! [C_42,A_43,B_44] :
      ( k1_mcart_1(C_42) != C_42
      | ~ m1_subset_1(C_42,k2_zfmisc_1(A_43,B_44))
      | k1_xboole_0 = B_44
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_118,plain,
    ( k1_mcart_1('#skF_4') != '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_115])).

tff(c_121,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_118])).

tff(c_122,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_6])).

tff(c_74,plain,(
    ! [A_31,C_32,B_33] :
      ( r2_hidden(k2_mcart_1(A_31),C_32)
      | ~ r2_hidden(A_31,k2_zfmisc_1(B_33,C_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_98,plain,(
    ! [B_40,C_41] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_40,C_41))),C_41)
      | v1_xboole_0(k2_zfmisc_1(B_40,C_41)) ) ),
    inference(resolution,[status(thm)],[c_4,c_74])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_151,plain,(
    ! [C_47,B_48] :
      ( ~ v1_xboole_0(C_47)
      | v1_xboole_0(k2_zfmisc_1(B_48,C_47)) ) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_125,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_8])).

tff(c_156,plain,(
    ! [B_49,C_50] :
      ( k2_zfmisc_1(B_49,C_50) = '#skF_2'
      | ~ v1_xboole_0(C_50) ) ),
    inference(resolution,[status(thm)],[c_151,c_125])).

tff(c_163,plain,(
    ! [B_51] : k2_zfmisc_1(B_51,'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_128,c_156])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( r2_hidden(k1_mcart_1(A_11),B_12)
      | ~ r2_hidden(A_11,k2_zfmisc_1(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_183,plain,(
    ! [A_52,B_53] :
      ( r2_hidden(k1_mcart_1(A_52),B_53)
      | ~ r2_hidden(A_52,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_18])).

tff(c_202,plain,(
    ! [B_53,A_52] :
      ( ~ v1_xboole_0(B_53)
      | ~ r2_hidden(A_52,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_183,c_2])).

tff(c_203,plain,(
    ! [A_52] : ~ r2_hidden(A_52,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_250,plain,(
    ! [C_57] : v1_xboole_0(k2_zfmisc_1('#skF_2',C_57)) ),
    inference(resolution,[status(thm)],[c_224,c_203])).

tff(c_260,plain,(
    ! [C_57] : k2_zfmisc_1('#skF_2',C_57) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_250,c_125])).

tff(c_28,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_126,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_28])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_126])).

tff(c_268,plain,(
    ! [B_53] : ~ v1_xboole_0(B_53) ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_268,c_128])).

tff(c_277,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_285,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_6])).

tff(c_308,plain,(
    ! [C_60,B_61] :
      ( ~ v1_xboole_0(C_60)
      | v1_xboole_0(k2_zfmisc_1(B_61,C_60)) ) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_282,plain,(
    ! [A_5] :
      ( A_5 = '#skF_3'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_8])).

tff(c_313,plain,(
    ! [B_62,C_63] :
      ( k2_zfmisc_1(B_62,C_63) = '#skF_3'
      | ~ v1_xboole_0(C_63) ) ),
    inference(resolution,[status(thm)],[c_308,c_282])).

tff(c_319,plain,(
    ! [B_62] : k2_zfmisc_1(B_62,'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_285,c_313])).

tff(c_283,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_28])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_283])).

tff(c_324,plain,(
    k2_mcart_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_456,plain,(
    ! [C_90,A_91,B_92] :
      ( k2_mcart_1(C_90) != C_90
      | ~ m1_subset_1(C_90,k2_zfmisc_1(A_91,B_92))
      | k1_xboole_0 = B_92
      | k1_xboole_0 = A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_462,plain,
    ( k2_mcart_1('#skF_4') != '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_456])).

tff(c_466,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_462])).

tff(c_486,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_466])).

tff(c_356,plain,(
    ! [A_70,C_71,B_72] :
      ( r2_hidden(k2_mcart_1(A_70),C_71)
      | ~ r2_hidden(A_70,k2_zfmisc_1(B_72,C_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_380,plain,(
    ! [B_78,C_79] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_78,C_79))),C_79)
      | v1_xboole_0(k2_zfmisc_1(B_78,C_79)) ) ),
    inference(resolution,[status(thm)],[c_4,c_356])).

tff(c_402,plain,(
    ! [C_83,B_84] :
      ( ~ v1_xboole_0(C_83)
      | v1_xboole_0(k2_zfmisc_1(B_84,C_83)) ) ),
    inference(resolution,[status(thm)],[c_380,c_2])).

tff(c_407,plain,(
    ! [B_85,C_86] :
      ( k2_zfmisc_1(B_85,C_86) = k1_xboole_0
      | ~ v1_xboole_0(C_86) ) ),
    inference(resolution,[status(thm)],[c_402,c_8])).

tff(c_414,plain,(
    ! [B_87] : k2_zfmisc_1(B_87,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_407])).

tff(c_438,plain,(
    ! [A_88,B_89] :
      ( r2_hidden(k1_mcart_1(A_88),B_89)
      | ~ r2_hidden(A_88,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_18])).

tff(c_454,plain,(
    ! [B_89,A_88] :
      ( ~ v1_xboole_0(B_89)
      | ~ r2_hidden(A_88,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_438,c_2])).

tff(c_455,plain,(
    ! [A_88] : ~ r2_hidden(A_88,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_454])).

tff(c_487,plain,(
    ! [A_88] : ~ r2_hidden(A_88,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_455])).

tff(c_589,plain,(
    ! [C_100] : v1_xboole_0(k2_zfmisc_1('#skF_2',C_100)) ),
    inference(resolution,[status(thm)],[c_562,c_487])).

tff(c_492,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_8])).

tff(c_596,plain,(
    ! [C_100] : k2_zfmisc_1('#skF_2',C_100) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_589,c_492])).

tff(c_493,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_28])).

tff(c_603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_493])).

tff(c_604,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_466])).

tff(c_413,plain,(
    ! [B_85] : k2_zfmisc_1(B_85,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_407])).

tff(c_608,plain,(
    ! [B_85] : k2_zfmisc_1(B_85,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_604,c_413])).

tff(c_612,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_28])).

tff(c_663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_612])).

tff(c_664,plain,(
    ! [B_89] : ~ v1_xboole_0(B_89) ),
    inference(splitRight,[status(thm)],[c_454])).

tff(c_672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_664,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:51:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.31  
% 2.26/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.26/1.32  
% 2.26/1.32  %Foreground sorts:
% 2.26/1.32  
% 2.26/1.32  
% 2.26/1.32  %Background operators:
% 2.26/1.32  
% 2.26/1.32  
% 2.26/1.32  %Foreground operators:
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.26/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.32  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.26/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.26/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.32  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.26/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.32  
% 2.52/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.52/1.33  tff(f_55, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.52/1.33  tff(f_85, negated_conjecture, ~(![A, B]: (~(k2_zfmisc_1(A, B) = k1_xboole_0) => (![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_mcart_1)).
% 2.52/1.33  tff(f_72, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_mcart_1)).
% 2.52/1.33  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.52/1.33  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.52/1.33  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.52/1.33  tff(c_371, plain, (![A_75, B_76, C_77]: (r2_hidden(k1_mcart_1(A_75), B_76) | ~r2_hidden(A_75, k2_zfmisc_1(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.33  tff(c_562, plain, (![B_98, C_99]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_98, C_99))), B_98) | v1_xboole_0(k2_zfmisc_1(B_98, C_99)))), inference(resolution, [status(thm)], [c_4, c_371])).
% 2.52/1.33  tff(c_83, plain, (![A_34, B_35, C_36]: (r2_hidden(k1_mcart_1(A_34), B_35) | ~r2_hidden(A_34, k2_zfmisc_1(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.33  tff(c_224, plain, (![B_55, C_56]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_55, C_56))), B_55) | v1_xboole_0(k2_zfmisc_1(B_55, C_56)))), inference(resolution, [status(thm)], [c_4, c_83])).
% 2.52/1.33  tff(c_24, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.52/1.33  tff(c_37, plain, (k1_mcart_1('#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_24])).
% 2.52/1.33  tff(c_26, plain, (m1_subset_1('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.52/1.33  tff(c_115, plain, (![C_42, A_43, B_44]: (k1_mcart_1(C_42)!=C_42 | ~m1_subset_1(C_42, k2_zfmisc_1(A_43, B_44)) | k1_xboole_0=B_44 | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.52/1.33  tff(c_118, plain, (k1_mcart_1('#skF_4')!='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_26, c_115])).
% 2.52/1.33  tff(c_121, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_37, c_118])).
% 2.52/1.33  tff(c_122, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_121])).
% 2.52/1.33  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.52/1.33  tff(c_128, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_6])).
% 2.52/1.33  tff(c_74, plain, (![A_31, C_32, B_33]: (r2_hidden(k2_mcart_1(A_31), C_32) | ~r2_hidden(A_31, k2_zfmisc_1(B_33, C_32)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.33  tff(c_98, plain, (![B_40, C_41]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_40, C_41))), C_41) | v1_xboole_0(k2_zfmisc_1(B_40, C_41)))), inference(resolution, [status(thm)], [c_4, c_74])).
% 2.52/1.33  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.52/1.33  tff(c_151, plain, (![C_47, B_48]: (~v1_xboole_0(C_47) | v1_xboole_0(k2_zfmisc_1(B_48, C_47)))), inference(resolution, [status(thm)], [c_98, c_2])).
% 2.52/1.33  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.52/1.33  tff(c_125, plain, (![A_5]: (A_5='#skF_2' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_8])).
% 2.52/1.33  tff(c_156, plain, (![B_49, C_50]: (k2_zfmisc_1(B_49, C_50)='#skF_2' | ~v1_xboole_0(C_50))), inference(resolution, [status(thm)], [c_151, c_125])).
% 2.52/1.33  tff(c_163, plain, (![B_51]: (k2_zfmisc_1(B_51, '#skF_2')='#skF_2')), inference(resolution, [status(thm)], [c_128, c_156])).
% 2.52/1.33  tff(c_18, plain, (![A_11, B_12, C_13]: (r2_hidden(k1_mcart_1(A_11), B_12) | ~r2_hidden(A_11, k2_zfmisc_1(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.33  tff(c_183, plain, (![A_52, B_53]: (r2_hidden(k1_mcart_1(A_52), B_53) | ~r2_hidden(A_52, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_18])).
% 2.52/1.33  tff(c_202, plain, (![B_53, A_52]: (~v1_xboole_0(B_53) | ~r2_hidden(A_52, '#skF_2'))), inference(resolution, [status(thm)], [c_183, c_2])).
% 2.52/1.33  tff(c_203, plain, (![A_52]: (~r2_hidden(A_52, '#skF_2'))), inference(splitLeft, [status(thm)], [c_202])).
% 2.52/1.33  tff(c_250, plain, (![C_57]: (v1_xboole_0(k2_zfmisc_1('#skF_2', C_57)))), inference(resolution, [status(thm)], [c_224, c_203])).
% 2.52/1.33  tff(c_260, plain, (![C_57]: (k2_zfmisc_1('#skF_2', C_57)='#skF_2')), inference(resolution, [status(thm)], [c_250, c_125])).
% 2.52/1.33  tff(c_28, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.52/1.33  tff(c_126, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_28])).
% 2.52/1.33  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_260, c_126])).
% 2.52/1.33  tff(c_268, plain, (![B_53]: (~v1_xboole_0(B_53))), inference(splitRight, [status(thm)], [c_202])).
% 2.52/1.33  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_268, c_128])).
% 2.52/1.33  tff(c_277, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_121])).
% 2.52/1.33  tff(c_285, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_277, c_6])).
% 2.52/1.33  tff(c_308, plain, (![C_60, B_61]: (~v1_xboole_0(C_60) | v1_xboole_0(k2_zfmisc_1(B_61, C_60)))), inference(resolution, [status(thm)], [c_98, c_2])).
% 2.52/1.33  tff(c_282, plain, (![A_5]: (A_5='#skF_3' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_277, c_8])).
% 2.52/1.33  tff(c_313, plain, (![B_62, C_63]: (k2_zfmisc_1(B_62, C_63)='#skF_3' | ~v1_xboole_0(C_63))), inference(resolution, [status(thm)], [c_308, c_282])).
% 2.52/1.33  tff(c_319, plain, (![B_62]: (k2_zfmisc_1(B_62, '#skF_3')='#skF_3')), inference(resolution, [status(thm)], [c_285, c_313])).
% 2.52/1.33  tff(c_283, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_277, c_28])).
% 2.52/1.33  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_319, c_283])).
% 2.52/1.33  tff(c_324, plain, (k2_mcart_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_24])).
% 2.52/1.33  tff(c_456, plain, (![C_90, A_91, B_92]: (k2_mcart_1(C_90)!=C_90 | ~m1_subset_1(C_90, k2_zfmisc_1(A_91, B_92)) | k1_xboole_0=B_92 | k1_xboole_0=A_91)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.52/1.33  tff(c_462, plain, (k2_mcart_1('#skF_4')!='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_26, c_456])).
% 2.52/1.33  tff(c_466, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_324, c_462])).
% 2.52/1.33  tff(c_486, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_466])).
% 2.52/1.33  tff(c_356, plain, (![A_70, C_71, B_72]: (r2_hidden(k2_mcart_1(A_70), C_71) | ~r2_hidden(A_70, k2_zfmisc_1(B_72, C_71)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.33  tff(c_380, plain, (![B_78, C_79]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_78, C_79))), C_79) | v1_xboole_0(k2_zfmisc_1(B_78, C_79)))), inference(resolution, [status(thm)], [c_4, c_356])).
% 2.52/1.33  tff(c_402, plain, (![C_83, B_84]: (~v1_xboole_0(C_83) | v1_xboole_0(k2_zfmisc_1(B_84, C_83)))), inference(resolution, [status(thm)], [c_380, c_2])).
% 2.52/1.33  tff(c_407, plain, (![B_85, C_86]: (k2_zfmisc_1(B_85, C_86)=k1_xboole_0 | ~v1_xboole_0(C_86))), inference(resolution, [status(thm)], [c_402, c_8])).
% 2.52/1.33  tff(c_414, plain, (![B_87]: (k2_zfmisc_1(B_87, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_407])).
% 2.52/1.33  tff(c_438, plain, (![A_88, B_89]: (r2_hidden(k1_mcart_1(A_88), B_89) | ~r2_hidden(A_88, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_414, c_18])).
% 2.52/1.33  tff(c_454, plain, (![B_89, A_88]: (~v1_xboole_0(B_89) | ~r2_hidden(A_88, k1_xboole_0))), inference(resolution, [status(thm)], [c_438, c_2])).
% 2.52/1.33  tff(c_455, plain, (![A_88]: (~r2_hidden(A_88, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_454])).
% 2.52/1.33  tff(c_487, plain, (![A_88]: (~r2_hidden(A_88, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_455])).
% 2.52/1.33  tff(c_589, plain, (![C_100]: (v1_xboole_0(k2_zfmisc_1('#skF_2', C_100)))), inference(resolution, [status(thm)], [c_562, c_487])).
% 2.52/1.33  tff(c_492, plain, (![A_5]: (A_5='#skF_2' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_8])).
% 2.52/1.33  tff(c_596, plain, (![C_100]: (k2_zfmisc_1('#skF_2', C_100)='#skF_2')), inference(resolution, [status(thm)], [c_589, c_492])).
% 2.52/1.33  tff(c_493, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_486, c_28])).
% 2.52/1.33  tff(c_603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_596, c_493])).
% 2.52/1.33  tff(c_604, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_466])).
% 2.52/1.33  tff(c_413, plain, (![B_85]: (k2_zfmisc_1(B_85, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_407])).
% 2.52/1.33  tff(c_608, plain, (![B_85]: (k2_zfmisc_1(B_85, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_604, c_604, c_413])).
% 2.52/1.33  tff(c_612, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_604, c_28])).
% 2.52/1.33  tff(c_663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_608, c_612])).
% 2.52/1.33  tff(c_664, plain, (![B_89]: (~v1_xboole_0(B_89))), inference(splitRight, [status(thm)], [c_454])).
% 2.52/1.33  tff(c_672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_664, c_6])).
% 2.52/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.33  
% 2.52/1.33  Inference rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Ref     : 0
% 2.52/1.33  #Sup     : 126
% 2.52/1.33  #Fact    : 0
% 2.52/1.33  #Define  : 0
% 2.52/1.33  #Split   : 6
% 2.52/1.33  #Chain   : 0
% 2.52/1.34  #Close   : 0
% 2.52/1.34  
% 2.52/1.34  Ordering : KBO
% 2.52/1.34  
% 2.52/1.34  Simplification rules
% 2.52/1.34  ----------------------
% 2.52/1.34  #Subsume      : 16
% 2.52/1.34  #Demod        : 100
% 2.52/1.34  #Tautology    : 64
% 2.52/1.34  #SimpNegUnit  : 17
% 2.52/1.34  #BackRed      : 53
% 2.52/1.34  
% 2.52/1.34  #Partial instantiations: 0
% 2.52/1.34  #Strategies tried      : 1
% 2.52/1.34  
% 2.52/1.34  Timing (in seconds)
% 2.52/1.34  ----------------------
% 2.52/1.34  Preprocessing        : 0.26
% 2.52/1.34  Parsing              : 0.15
% 2.52/1.34  CNF conversion       : 0.02
% 2.52/1.34  Main loop            : 0.29
% 2.52/1.34  Inferencing          : 0.12
% 2.52/1.34  Reduction            : 0.08
% 2.52/1.34  Demodulation         : 0.06
% 2.52/1.34  BG Simplification    : 0.02
% 2.52/1.34  Subsumption          : 0.05
% 2.52/1.34  Abstraction          : 0.01
% 2.52/1.34  MUC search           : 0.00
% 2.52/1.34  Cooper               : 0.00
% 2.52/1.34  Total                : 0.59
% 2.52/1.34  Index Insertion      : 0.00
% 2.52/1.34  Index Deletion       : 0.00
% 2.52/1.34  Index Matching       : 0.00
% 2.52/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
