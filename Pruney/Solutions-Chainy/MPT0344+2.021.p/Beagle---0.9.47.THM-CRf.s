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
% DateTime   : Thu Dec  3 09:55:22 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 288 expanded)
%              Number of leaves         :   17 (  99 expanded)
%              Depth                    :   14
%              Number of atoms          :  139 ( 724 expanded)
%              Number of equality atoms :   15 (  97 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( m1_subset_1(B_8,A_7)
      | ~ v1_xboole_0(B_8)
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_49,plain,(
    ! [B_21,A_22] :
      ( m1_subset_1(B_21,A_22)
      | ~ v1_xboole_0(B_21)
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_35,plain,(
    ! [C_20] :
      ( ~ r2_hidden(C_20,'#skF_4')
      | ~ m1_subset_1(C_20,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_43,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_35])).

tff(c_47,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_43])).

tff(c_57,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_4'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_49,c_47])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [B_25,A_26] :
      ( m1_subset_1(B_25,A_26)
      | ~ r2_hidden(B_25,A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_75,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_83,plain,(
    ! [B_28,A_29] :
      ( r2_hidden(B_28,A_29)
      | ~ m1_subset_1(B_28,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [C_14] :
      ( ~ r2_hidden(C_14,'#skF_4')
      | ~ m1_subset_1(C_14,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_95,plain,(
    ! [B_28] :
      ( ~ m1_subset_1(B_28,'#skF_3')
      | ~ m1_subset_1(B_28,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_83,c_18])).

tff(c_103,plain,(
    ! [B_31] :
      ( ~ m1_subset_1(B_31,'#skF_3')
      | ~ m1_subset_1(B_31,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_111,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_103])).

tff(c_121,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_111])).

tff(c_126,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_3'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_121])).

tff(c_127,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_76,plain,(
    ! [A_5] :
      ( m1_subset_1('#skF_2'(A_5),A_5)
      | v1_xboole_0(A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r2_hidden(B_8,A_7)
      | ~ m1_subset_1(B_8,A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_128,plain,(
    ! [C_32,A_33,B_34] :
      ( r2_hidden(C_32,A_33)
      | ~ r2_hidden(C_32,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_246,plain,(
    ! [B_45,A_46,A_47] :
      ( r2_hidden(B_45,A_46)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_45,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_10,c_128])).

tff(c_257,plain,(
    ! [B_45] :
      ( r2_hidden(B_45,'#skF_3')
      | ~ m1_subset_1(B_45,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_246])).

tff(c_264,plain,(
    ! [B_48] :
      ( r2_hidden(B_48,'#skF_3')
      | ~ m1_subset_1(B_48,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_257])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( m1_subset_1(B_8,A_7)
      | ~ r2_hidden(B_8,A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_269,plain,(
    ! [B_48] :
      ( m1_subset_1(B_48,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_264,c_8])).

tff(c_278,plain,(
    ! [B_49] :
      ( m1_subset_1(B_49,'#skF_3')
      | ~ m1_subset_1(B_49,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_269])).

tff(c_102,plain,(
    ! [B_28] :
      ( ~ m1_subset_1(B_28,'#skF_3')
      | ~ m1_subset_1(B_28,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_295,plain,(
    ! [B_50] : ~ m1_subset_1(B_50,'#skF_4') ),
    inference(resolution,[status(thm)],[c_278,c_102])).

tff(c_299,plain,
    ( v1_xboole_0('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_76,c_295])).

tff(c_311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_127,c_299])).

tff(c_313,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_24,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(resolution,[status(thm)],[c_24,c_2])).

tff(c_317,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_313,c_28])).

tff(c_321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_317])).

tff(c_322,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_325,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_322,c_28])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_325])).

tff(c_331,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_335,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_331,c_28])).

tff(c_338,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_20])).

tff(c_386,plain,(
    ! [B_58,A_59] :
      ( r2_hidden(B_58,A_59)
      | ~ m1_subset_1(B_58,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_398,plain,(
    ! [B_58] :
      ( ~ m1_subset_1(B_58,'#skF_3')
      | ~ m1_subset_1(B_58,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_386,c_18])).

tff(c_411,plain,(
    ! [B_63] :
      ( ~ m1_subset_1(B_63,'#skF_3')
      | ~ m1_subset_1(B_63,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_398])).

tff(c_419,plain,(
    ! [B_8] :
      ( ~ m1_subset_1(B_8,'#skF_4')
      | ~ v1_xboole_0(B_8)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_411])).

tff(c_425,plain,(
    ! [B_64] :
      ( ~ m1_subset_1(B_64,'#skF_4')
      | ~ v1_xboole_0(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_419])).

tff(c_435,plain,(
    ! [B_8] :
      ( ~ v1_xboole_0(B_8)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_425])).

tff(c_436,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_435])).

tff(c_400,plain,(
    ! [C_60,A_61,B_62] :
      ( r2_hidden(C_60,A_61)
      | ~ r2_hidden(C_60,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_455,plain,(
    ! [A_66,A_67] :
      ( r2_hidden('#skF_1'(A_66),A_67)
      | ~ m1_subset_1(A_66,k1_zfmisc_1(A_67))
      | v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_4,c_400])).

tff(c_472,plain,(
    ! [A_68,A_69] :
      ( ~ v1_xboole_0(A_68)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(A_68))
      | v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_455,c_2])).

tff(c_487,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_472])).

tff(c_493,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_487])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_436,c_493])).

tff(c_497,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_435])).

tff(c_336,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | A_17 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_28])).

tff(c_500,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_497,c_336])).

tff(c_504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_500])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.29  
% 2.03/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.29  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.03/1.29  
% 2.03/1.29  %Foreground sorts:
% 2.03/1.29  
% 2.03/1.29  
% 2.03/1.29  %Background operators:
% 2.03/1.29  
% 2.03/1.29  
% 2.03/1.29  %Foreground operators:
% 2.03/1.29  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.03/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.03/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.29  
% 2.03/1.30  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 2.03/1.30  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.03/1.30  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.03/1.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.03/1.30  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.03/1.30  tff(c_20, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.03/1.30  tff(c_12, plain, (![B_8, A_7]: (m1_subset_1(B_8, A_7) | ~v1_xboole_0(B_8) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.03/1.30  tff(c_49, plain, (![B_21, A_22]: (m1_subset_1(B_21, A_22) | ~v1_xboole_0(B_21) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.03/1.30  tff(c_6, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.03/1.30  tff(c_35, plain, (![C_20]: (~r2_hidden(C_20, '#skF_4') | ~m1_subset_1(C_20, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.03/1.30  tff(c_43, plain, (~m1_subset_1('#skF_2'('#skF_4'), '#skF_3') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_6, c_35])).
% 2.03/1.30  tff(c_47, plain, (~m1_subset_1('#skF_2'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_20, c_43])).
% 2.03/1.30  tff(c_57, plain, (~v1_xboole_0('#skF_2'('#skF_4')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_49, c_47])).
% 2.03/1.30  tff(c_58, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_57])).
% 2.03/1.30  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.30  tff(c_68, plain, (![B_25, A_26]: (m1_subset_1(B_25, A_26) | ~r2_hidden(B_25, A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.03/1.30  tff(c_75, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_68])).
% 2.03/1.30  tff(c_83, plain, (![B_28, A_29]: (r2_hidden(B_28, A_29) | ~m1_subset_1(B_28, A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.03/1.30  tff(c_18, plain, (![C_14]: (~r2_hidden(C_14, '#skF_4') | ~m1_subset_1(C_14, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.03/1.30  tff(c_95, plain, (![B_28]: (~m1_subset_1(B_28, '#skF_3') | ~m1_subset_1(B_28, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_83, c_18])).
% 2.03/1.30  tff(c_103, plain, (![B_31]: (~m1_subset_1(B_31, '#skF_3') | ~m1_subset_1(B_31, '#skF_4'))), inference(splitLeft, [status(thm)], [c_95])).
% 2.03/1.30  tff(c_111, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_75, c_103])).
% 2.03/1.30  tff(c_121, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_111])).
% 2.03/1.30  tff(c_126, plain, (~v1_xboole_0('#skF_1'('#skF_3')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_12, c_121])).
% 2.03/1.30  tff(c_127, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_126])).
% 2.03/1.30  tff(c_76, plain, (![A_5]: (m1_subset_1('#skF_2'(A_5), A_5) | v1_xboole_0(A_5) | k1_xboole_0=A_5)), inference(resolution, [status(thm)], [c_6, c_68])).
% 2.03/1.30  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.03/1.30  tff(c_10, plain, (![B_8, A_7]: (r2_hidden(B_8, A_7) | ~m1_subset_1(B_8, A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.03/1.30  tff(c_128, plain, (![C_32, A_33, B_34]: (r2_hidden(C_32, A_33) | ~r2_hidden(C_32, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.03/1.30  tff(c_246, plain, (![B_45, A_46, A_47]: (r2_hidden(B_45, A_46) | ~m1_subset_1(A_47, k1_zfmisc_1(A_46)) | ~m1_subset_1(B_45, A_47) | v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_10, c_128])).
% 2.03/1.30  tff(c_257, plain, (![B_45]: (r2_hidden(B_45, '#skF_3') | ~m1_subset_1(B_45, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_246])).
% 2.03/1.30  tff(c_264, plain, (![B_48]: (r2_hidden(B_48, '#skF_3') | ~m1_subset_1(B_48, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_127, c_257])).
% 2.03/1.30  tff(c_8, plain, (![B_8, A_7]: (m1_subset_1(B_8, A_7) | ~r2_hidden(B_8, A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.03/1.30  tff(c_269, plain, (![B_48]: (m1_subset_1(B_48, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_48, '#skF_4'))), inference(resolution, [status(thm)], [c_264, c_8])).
% 2.03/1.30  tff(c_278, plain, (![B_49]: (m1_subset_1(B_49, '#skF_3') | ~m1_subset_1(B_49, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_269])).
% 2.03/1.30  tff(c_102, plain, (![B_28]: (~m1_subset_1(B_28, '#skF_3') | ~m1_subset_1(B_28, '#skF_4'))), inference(splitLeft, [status(thm)], [c_95])).
% 2.03/1.30  tff(c_295, plain, (![B_50]: (~m1_subset_1(B_50, '#skF_4'))), inference(resolution, [status(thm)], [c_278, c_102])).
% 2.03/1.30  tff(c_299, plain, (v1_xboole_0('#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_76, c_295])).
% 2.03/1.30  tff(c_311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_127, c_299])).
% 2.03/1.30  tff(c_313, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_126])).
% 2.03/1.30  tff(c_24, plain, (![A_17]: (r2_hidden('#skF_2'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.03/1.30  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.30  tff(c_28, plain, (![A_17]: (~v1_xboole_0(A_17) | k1_xboole_0=A_17)), inference(resolution, [status(thm)], [c_24, c_2])).
% 2.03/1.30  tff(c_317, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_313, c_28])).
% 2.03/1.30  tff(c_321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_317])).
% 2.03/1.30  tff(c_322, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_95])).
% 2.03/1.30  tff(c_325, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_322, c_28])).
% 2.03/1.30  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_325])).
% 2.03/1.30  tff(c_331, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_57])).
% 2.03/1.30  tff(c_335, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_331, c_28])).
% 2.03/1.30  tff(c_338, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_335, c_20])).
% 2.03/1.30  tff(c_386, plain, (![B_58, A_59]: (r2_hidden(B_58, A_59) | ~m1_subset_1(B_58, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.03/1.30  tff(c_398, plain, (![B_58]: (~m1_subset_1(B_58, '#skF_3') | ~m1_subset_1(B_58, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_386, c_18])).
% 2.03/1.30  tff(c_411, plain, (![B_63]: (~m1_subset_1(B_63, '#skF_3') | ~m1_subset_1(B_63, '#skF_4'))), inference(splitLeft, [status(thm)], [c_398])).
% 2.03/1.30  tff(c_419, plain, (![B_8]: (~m1_subset_1(B_8, '#skF_4') | ~v1_xboole_0(B_8) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_411])).
% 2.03/1.30  tff(c_425, plain, (![B_64]: (~m1_subset_1(B_64, '#skF_4') | ~v1_xboole_0(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_331, c_419])).
% 2.03/1.30  tff(c_435, plain, (![B_8]: (~v1_xboole_0(B_8) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_425])).
% 2.03/1.30  tff(c_436, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_435])).
% 2.03/1.30  tff(c_400, plain, (![C_60, A_61, B_62]: (r2_hidden(C_60, A_61) | ~r2_hidden(C_60, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.03/1.30  tff(c_455, plain, (![A_66, A_67]: (r2_hidden('#skF_1'(A_66), A_67) | ~m1_subset_1(A_66, k1_zfmisc_1(A_67)) | v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_4, c_400])).
% 2.03/1.30  tff(c_472, plain, (![A_68, A_69]: (~v1_xboole_0(A_68) | ~m1_subset_1(A_69, k1_zfmisc_1(A_68)) | v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_455, c_2])).
% 2.03/1.30  tff(c_487, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_22, c_472])).
% 2.03/1.30  tff(c_493, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_331, c_487])).
% 2.03/1.30  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_436, c_493])).
% 2.03/1.30  tff(c_497, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_435])).
% 2.03/1.30  tff(c_336, plain, (![A_17]: (~v1_xboole_0(A_17) | A_17='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_28])).
% 2.03/1.30  tff(c_500, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_497, c_336])).
% 2.03/1.30  tff(c_504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_338, c_500])).
% 2.03/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.30  
% 2.03/1.30  Inference rules
% 2.03/1.30  ----------------------
% 2.03/1.30  #Ref     : 0
% 2.03/1.30  #Sup     : 95
% 2.03/1.30  #Fact    : 0
% 2.03/1.30  #Define  : 0
% 2.03/1.30  #Split   : 10
% 2.03/1.30  #Chain   : 0
% 2.03/1.30  #Close   : 0
% 2.03/1.30  
% 2.03/1.30  Ordering : KBO
% 2.03/1.30  
% 2.03/1.30  Simplification rules
% 2.03/1.30  ----------------------
% 2.03/1.30  #Subsume      : 20
% 2.03/1.30  #Demod        : 8
% 2.03/1.30  #Tautology    : 19
% 2.03/1.30  #SimpNegUnit  : 14
% 2.03/1.30  #BackRed      : 3
% 2.03/1.30  
% 2.03/1.30  #Partial instantiations: 0
% 2.03/1.30  #Strategies tried      : 1
% 2.03/1.30  
% 2.03/1.30  Timing (in seconds)
% 2.03/1.30  ----------------------
% 2.03/1.31  Preprocessing        : 0.26
% 2.03/1.31  Parsing              : 0.14
% 2.03/1.31  CNF conversion       : 0.02
% 2.39/1.31  Main loop            : 0.25
% 2.39/1.31  Inferencing          : 0.10
% 2.39/1.31  Reduction            : 0.06
% 2.39/1.31  Demodulation         : 0.03
% 2.39/1.31  BG Simplification    : 0.02
% 2.39/1.31  Subsumption          : 0.06
% 2.39/1.31  Abstraction          : 0.01
% 2.39/1.31  MUC search           : 0.00
% 2.39/1.31  Cooper               : 0.00
% 2.39/1.31  Total                : 0.55
% 2.39/1.31  Index Insertion      : 0.00
% 2.39/1.31  Index Deletion       : 0.00
% 2.39/1.31  Index Matching       : 0.00
% 2.39/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
