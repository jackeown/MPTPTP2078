%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:16 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 168 expanded)
%              Number of leaves         :   17 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  124 ( 463 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                   => r2_hidden(D,C) ) )
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_20,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_60,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_1'(A_30,B_31),A_30)
      | r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_76,plain,(
    ! [A_33,B_34] :
      ( ~ v1_xboole_0(A_33)
      | r1_tarski(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_60,c_8])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_20])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [B_35,A_36] :
      ( m1_subset_1(B_35,A_36)
      | ~ r2_hidden(B_35,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_88,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ v1_xboole_0(B_9)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_45,plain,(
    ! [B_28,A_29] :
      ( r2_hidden(B_28,A_29)
      | ~ m1_subset_1(B_28,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    ! [D_18] :
      ( r2_hidden(D_18,'#skF_4')
      | ~ r2_hidden(D_18,'#skF_3')
      | ~ m1_subset_1(D_18,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_58,plain,(
    ! [B_28] :
      ( r2_hidden(B_28,'#skF_4')
      | ~ m1_subset_1(B_28,'#skF_2')
      | ~ m1_subset_1(B_28,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_45,c_22])).

tff(c_105,plain,(
    ! [B_43] :
      ( r2_hidden(B_43,'#skF_4')
      | ~ m1_subset_1(B_43,'#skF_2')
      | ~ m1_subset_1(B_43,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_58])).

tff(c_124,plain,(
    ! [B_43] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_43,'#skF_2')
      | ~ m1_subset_1(B_43,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_105,c_8])).

tff(c_125,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ r2_hidden(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_122,plain,(
    ! [B_43] :
      ( m1_subset_1(B_43,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_43,'#skF_2')
      | ~ m1_subset_1(B_43,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_105,c_10])).

tff(c_183,plain,(
    ! [B_57] :
      ( m1_subset_1(B_57,'#skF_4')
      | ~ m1_subset_1(B_57,'#skF_2')
      | ~ m1_subset_1(B_57,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_122])).

tff(c_193,plain,(
    ! [B_9] :
      ( m1_subset_1(B_9,'#skF_4')
      | ~ m1_subset_1(B_9,'#skF_3')
      | ~ v1_xboole_0(B_9)
      | ~ v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_183])).

tff(c_194,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(B_9,A_8)
      | ~ m1_subset_1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_97,plain,(
    ! [C_40,A_41,B_42] :
      ( r2_hidden(C_40,A_41)
      | ~ r2_hidden(C_40,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_223,plain,(
    ! [B_59,A_60,A_61] :
      ( r2_hidden(B_59,A_60)
      | ~ m1_subset_1(A_61,k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_59,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_12,c_97])).

tff(c_233,plain,(
    ! [B_59] :
      ( r2_hidden(B_59,'#skF_2')
      | ~ m1_subset_1(B_59,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_223])).

tff(c_242,plain,(
    ! [B_62] :
      ( r2_hidden(B_62,'#skF_2')
      | ~ m1_subset_1(B_62,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_233])).

tff(c_249,plain,(
    ! [B_62] :
      ( m1_subset_1(B_62,'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_62,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_242,c_10])).

tff(c_311,plain,(
    ! [B_67] :
      ( m1_subset_1(B_67,'#skF_2')
      | ~ m1_subset_1(B_67,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_249])).

tff(c_195,plain,(
    ! [B_58] :
      ( r2_hidden('#skF_1'('#skF_3',B_58),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_58),'#skF_2')
      | r1_tarski('#skF_3',B_58) ) ),
    inference(resolution,[status(thm)],[c_60,c_22])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_206,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_195,c_4])).

tff(c_217,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_20,c_206])).

tff(c_325,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_311,c_217])).

tff(c_333,plain,
    ( v1_xboole_0('#skF_3')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_325])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_80,c_333])).

tff(c_342,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_386,plain,(
    ! [A_70,B_71,A_72] :
      ( r2_hidden('#skF_1'(A_70,B_71),A_72)
      | ~ m1_subset_1(A_70,k1_zfmisc_1(A_72))
      | r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_411,plain,(
    ! [A_73,A_74] :
      ( ~ m1_subset_1(A_73,k1_zfmisc_1(A_74))
      | r1_tarski(A_73,A_74) ) ),
    inference(resolution,[status(thm)],[c_386,c_4])).

tff(c_429,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_411])).

tff(c_90,plain,(
    ! [C_37,B_38,A_39] :
      ( r2_hidden(C_37,B_38)
      | ~ r2_hidden(C_37,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_143,plain,(
    ! [A_48,B_49,B_50] :
      ( r2_hidden('#skF_1'(A_48,B_49),B_50)
      | ~ r1_tarski(A_48,B_50)
      | r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_167,plain,(
    ! [B_50,A_48,B_49] :
      ( ~ v1_xboole_0(B_50)
      | ~ r1_tarski(A_48,B_50)
      | r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_143,c_8])).

tff(c_460,plain,(
    ! [B_49] :
      ( ~ v1_xboole_0('#skF_2')
      | r1_tarski('#skF_3',B_49) ) ),
    inference(resolution,[status(thm)],[c_429,c_167])).

tff(c_465,plain,(
    ! [B_49] : r1_tarski('#skF_3',B_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_460])).

tff(c_508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:02:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.37  
% 2.54/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.37  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.54/1.37  
% 2.54/1.37  %Foreground sorts:
% 2.54/1.37  
% 2.54/1.37  
% 2.54/1.37  %Background operators:
% 2.54/1.37  
% 2.54/1.37  
% 2.54/1.37  %Foreground operators:
% 2.54/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.54/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.37  
% 2.54/1.39  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 2.54/1.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.54/1.39  tff(f_37, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 2.54/1.39  tff(f_50, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.54/1.39  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.54/1.39  tff(c_20, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.54/1.39  tff(c_60, plain, (![A_30, B_31]: (r2_hidden('#skF_1'(A_30, B_31), A_30) | r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.54/1.39  tff(c_8, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.54/1.39  tff(c_76, plain, (![A_33, B_34]: (~v1_xboole_0(A_33) | r1_tarski(A_33, B_34))), inference(resolution, [status(thm)], [c_60, c_8])).
% 2.54/1.39  tff(c_80, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_20])).
% 2.54/1.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.54/1.39  tff(c_81, plain, (![B_35, A_36]: (m1_subset_1(B_35, A_36) | ~r2_hidden(B_35, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.39  tff(c_88, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_81])).
% 2.54/1.39  tff(c_14, plain, (![B_9, A_8]: (m1_subset_1(B_9, A_8) | ~v1_xboole_0(B_9) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.39  tff(c_45, plain, (![B_28, A_29]: (r2_hidden(B_28, A_29) | ~m1_subset_1(B_28, A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.39  tff(c_22, plain, (![D_18]: (r2_hidden(D_18, '#skF_4') | ~r2_hidden(D_18, '#skF_3') | ~m1_subset_1(D_18, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.54/1.39  tff(c_58, plain, (![B_28]: (r2_hidden(B_28, '#skF_4') | ~m1_subset_1(B_28, '#skF_2') | ~m1_subset_1(B_28, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_45, c_22])).
% 2.54/1.39  tff(c_105, plain, (![B_43]: (r2_hidden(B_43, '#skF_4') | ~m1_subset_1(B_43, '#skF_2') | ~m1_subset_1(B_43, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_80, c_58])).
% 2.54/1.39  tff(c_124, plain, (![B_43]: (~v1_xboole_0('#skF_4') | ~m1_subset_1(B_43, '#skF_2') | ~m1_subset_1(B_43, '#skF_3'))), inference(resolution, [status(thm)], [c_105, c_8])).
% 2.54/1.39  tff(c_125, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_124])).
% 2.54/1.39  tff(c_10, plain, (![B_9, A_8]: (m1_subset_1(B_9, A_8) | ~r2_hidden(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.39  tff(c_122, plain, (![B_43]: (m1_subset_1(B_43, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_43, '#skF_2') | ~m1_subset_1(B_43, '#skF_3'))), inference(resolution, [status(thm)], [c_105, c_10])).
% 2.54/1.39  tff(c_183, plain, (![B_57]: (m1_subset_1(B_57, '#skF_4') | ~m1_subset_1(B_57, '#skF_2') | ~m1_subset_1(B_57, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_125, c_122])).
% 2.54/1.39  tff(c_193, plain, (![B_9]: (m1_subset_1(B_9, '#skF_4') | ~m1_subset_1(B_9, '#skF_3') | ~v1_xboole_0(B_9) | ~v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_183])).
% 2.54/1.39  tff(c_194, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_193])).
% 2.54/1.39  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.54/1.39  tff(c_12, plain, (![B_9, A_8]: (r2_hidden(B_9, A_8) | ~m1_subset_1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.39  tff(c_97, plain, (![C_40, A_41, B_42]: (r2_hidden(C_40, A_41) | ~r2_hidden(C_40, B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.54/1.39  tff(c_223, plain, (![B_59, A_60, A_61]: (r2_hidden(B_59, A_60) | ~m1_subset_1(A_61, k1_zfmisc_1(A_60)) | ~m1_subset_1(B_59, A_61) | v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_12, c_97])).
% 2.54/1.39  tff(c_233, plain, (![B_59]: (r2_hidden(B_59, '#skF_2') | ~m1_subset_1(B_59, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_223])).
% 2.54/1.39  tff(c_242, plain, (![B_62]: (r2_hidden(B_62, '#skF_2') | ~m1_subset_1(B_62, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_80, c_233])).
% 2.54/1.39  tff(c_249, plain, (![B_62]: (m1_subset_1(B_62, '#skF_2') | v1_xboole_0('#skF_2') | ~m1_subset_1(B_62, '#skF_3'))), inference(resolution, [status(thm)], [c_242, c_10])).
% 2.54/1.39  tff(c_311, plain, (![B_67]: (m1_subset_1(B_67, '#skF_2') | ~m1_subset_1(B_67, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_194, c_249])).
% 2.54/1.39  tff(c_195, plain, (![B_58]: (r2_hidden('#skF_1'('#skF_3', B_58), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', B_58), '#skF_2') | r1_tarski('#skF_3', B_58))), inference(resolution, [status(thm)], [c_60, c_22])).
% 2.54/1.39  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.54/1.39  tff(c_206, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_195, c_4])).
% 2.54/1.39  tff(c_217, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_20, c_20, c_206])).
% 2.54/1.39  tff(c_325, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_311, c_217])).
% 2.54/1.39  tff(c_333, plain, (v1_xboole_0('#skF_3') | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_88, c_325])).
% 2.54/1.39  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_80, c_333])).
% 2.54/1.39  tff(c_342, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_193])).
% 2.54/1.39  tff(c_386, plain, (![A_70, B_71, A_72]: (r2_hidden('#skF_1'(A_70, B_71), A_72) | ~m1_subset_1(A_70, k1_zfmisc_1(A_72)) | r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_6, c_97])).
% 2.54/1.39  tff(c_411, plain, (![A_73, A_74]: (~m1_subset_1(A_73, k1_zfmisc_1(A_74)) | r1_tarski(A_73, A_74))), inference(resolution, [status(thm)], [c_386, c_4])).
% 2.54/1.39  tff(c_429, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_411])).
% 2.54/1.39  tff(c_90, plain, (![C_37, B_38, A_39]: (r2_hidden(C_37, B_38) | ~r2_hidden(C_37, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.54/1.39  tff(c_143, plain, (![A_48, B_49, B_50]: (r2_hidden('#skF_1'(A_48, B_49), B_50) | ~r1_tarski(A_48, B_50) | r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_6, c_90])).
% 2.54/1.39  tff(c_167, plain, (![B_50, A_48, B_49]: (~v1_xboole_0(B_50) | ~r1_tarski(A_48, B_50) | r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_143, c_8])).
% 2.54/1.39  tff(c_460, plain, (![B_49]: (~v1_xboole_0('#skF_2') | r1_tarski('#skF_3', B_49))), inference(resolution, [status(thm)], [c_429, c_167])).
% 2.54/1.39  tff(c_465, plain, (![B_49]: (r1_tarski('#skF_3', B_49))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_460])).
% 2.54/1.39  tff(c_508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_465, c_20])).
% 2.54/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.39  
% 2.54/1.39  Inference rules
% 2.54/1.39  ----------------------
% 2.54/1.39  #Ref     : 0
% 2.54/1.39  #Sup     : 101
% 2.54/1.39  #Fact    : 0
% 2.54/1.39  #Define  : 0
% 2.54/1.39  #Split   : 3
% 2.54/1.39  #Chain   : 0
% 2.54/1.39  #Close   : 0
% 2.54/1.39  
% 2.54/1.39  Ordering : KBO
% 2.54/1.39  
% 2.54/1.39  Simplification rules
% 2.54/1.39  ----------------------
% 2.54/1.39  #Subsume      : 14
% 2.54/1.39  #Demod        : 10
% 2.54/1.39  #Tautology    : 13
% 2.54/1.39  #SimpNegUnit  : 19
% 2.54/1.39  #BackRed      : 1
% 2.54/1.39  
% 2.54/1.39  #Partial instantiations: 0
% 2.54/1.39  #Strategies tried      : 1
% 2.54/1.39  
% 2.54/1.39  Timing (in seconds)
% 2.54/1.39  ----------------------
% 2.54/1.39  Preprocessing        : 0.28
% 2.54/1.39  Parsing              : 0.16
% 2.54/1.39  CNF conversion       : 0.02
% 2.54/1.39  Main loop            : 0.30
% 2.54/1.39  Inferencing          : 0.12
% 2.54/1.39  Reduction            : 0.07
% 2.54/1.39  Demodulation         : 0.04
% 2.54/1.39  BG Simplification    : 0.02
% 2.54/1.39  Subsumption          : 0.07
% 2.54/1.39  Abstraction          : 0.01
% 2.54/1.39  MUC search           : 0.00
% 2.54/1.39  Cooper               : 0.00
% 2.54/1.39  Total                : 0.62
% 2.54/1.39  Index Insertion      : 0.00
% 2.54/1.39  Index Deletion       : 0.00
% 2.54/1.39  Index Matching       : 0.00
% 2.54/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
