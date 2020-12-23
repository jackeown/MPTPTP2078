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
% DateTime   : Thu Dec  3 09:55:16 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 158 expanded)
%              Number of leaves         :   20 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  123 ( 403 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                   => r2_hidden(D,C) ) )
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_66,plain,(
    ! [A_33,B_34] :
      ( r2_hidden('#skF_1'(A_33,B_34),A_33)
      | r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_81,plain,(
    ! [A_35,B_36] :
      ( ~ v1_xboole_0(A_35)
      | r1_tarski(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_66,c_8])).

tff(c_32,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_85,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_81,c_32])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_451,plain,(
    ! [B_82,A_83] :
      ( m1_subset_1(B_82,A_83)
      | ~ r2_hidden(B_82,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_470,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_451])).

tff(c_153,plain,(
    ! [B_45,A_46] :
      ( m1_subset_1(B_45,A_46)
      | ~ r2_hidden(B_45,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_168,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_153])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( m1_subset_1(B_14,A_13)
      | ~ v1_xboole_0(B_14)
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [D_20] :
      ( r2_hidden(D_20,'#skF_6')
      | ~ r2_hidden(D_20,'#skF_5')
      | ~ m1_subset_1(D_20,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_136,plain,(
    ! [B_44] :
      ( r2_hidden('#skF_1'('#skF_5',B_44),'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_5',B_44),'#skF_4')
      | r1_tarski('#skF_5',B_44) ) ),
    inference(resolution,[status(thm)],[c_66,c_34])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_140,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5','#skF_6'),'#skF_4')
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_136,c_4])).

tff(c_146,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_140])).

tff(c_151,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5','#skF_6'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_146])).

tff(c_152,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    ! [A_15] : ~ v1_xboole_0(k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_86,plain,(
    ! [B_37,A_38] :
      ( r2_hidden(B_37,A_38)
      | ~ m1_subset_1(B_37,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [C_12,A_8] :
      ( r1_tarski(C_12,A_8)
      | ~ r2_hidden(C_12,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_94,plain,(
    ! [B_37,A_8] :
      ( r1_tarski(B_37,A_8)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_8))
      | v1_xboole_0(k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_86,c_10])).

tff(c_105,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(B_39,A_40)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_94])).

tff(c_117,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_105])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( r2_hidden(B_14,A_13)
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_181,plain,(
    ! [C_49,B_50,A_51] :
      ( r2_hidden(C_49,B_50)
      | ~ r2_hidden(C_49,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_277,plain,(
    ! [B_68,B_69,A_70] :
      ( r2_hidden(B_68,B_69)
      | ~ r1_tarski(A_70,B_69)
      | ~ m1_subset_1(B_68,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_24,c_181])).

tff(c_281,plain,(
    ! [B_68] :
      ( r2_hidden(B_68,'#skF_4')
      | ~ m1_subset_1(B_68,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_117,c_277])).

tff(c_297,plain,(
    ! [B_71] :
      ( r2_hidden(B_71,'#skF_4')
      | ~ m1_subset_1(B_71,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_281])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( m1_subset_1(B_14,A_13)
      | ~ r2_hidden(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_305,plain,(
    ! [B_71] :
      ( m1_subset_1(B_71,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_71,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_297,c_22])).

tff(c_355,plain,(
    ! [B_74] :
      ( m1_subset_1(B_74,'#skF_4')
      | ~ m1_subset_1(B_74,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_305])).

tff(c_359,plain,(
    ! [B_2] :
      ( m1_subset_1('#skF_1'('#skF_5',B_2),'#skF_4')
      | v1_xboole_0('#skF_5')
      | r1_tarski('#skF_5',B_2) ) ),
    inference(resolution,[status(thm)],[c_168,c_355])).

tff(c_421,plain,(
    ! [B_80] :
      ( m1_subset_1('#skF_1'('#skF_5',B_80),'#skF_4')
      | r1_tarski('#skF_5',B_80) ) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_359])).

tff(c_428,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_421,c_146])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_428])).

tff(c_440,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_484,plain,(
    ! [C_86,B_87,A_88] :
      ( r2_hidden(C_86,B_87)
      | ~ r2_hidden(C_86,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_559,plain,(
    ! [B_104,B_105,A_106] :
      ( r2_hidden(B_104,B_105)
      | ~ r1_tarski(A_106,B_105)
      | ~ m1_subset_1(B_104,A_106)
      | v1_xboole_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_24,c_484])).

tff(c_563,plain,(
    ! [B_104] :
      ( r2_hidden(B_104,'#skF_4')
      | ~ m1_subset_1(B_104,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_117,c_559])).

tff(c_592,plain,(
    ! [B_109] :
      ( r2_hidden(B_109,'#skF_4')
      | ~ m1_subset_1(B_109,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_563])).

tff(c_607,plain,(
    ! [B_109] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_109,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_592,c_8])).

tff(c_616,plain,(
    ! [B_110] : ~ m1_subset_1(B_110,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_607])).

tff(c_620,plain,(
    ! [B_2] :
      ( v1_xboole_0('#skF_5')
      | r1_tarski('#skF_5',B_2) ) ),
    inference(resolution,[status(thm)],[c_470,c_616])).

tff(c_627,plain,(
    ! [B_2] : r1_tarski('#skF_5',B_2) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_620])).

tff(c_633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:31:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.37  
% 2.61/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.38  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.61/1.38  
% 2.61/1.38  %Foreground sorts:
% 2.61/1.38  
% 2.61/1.38  
% 2.61/1.38  %Background operators:
% 2.61/1.38  
% 2.61/1.38  
% 2.61/1.38  %Foreground operators:
% 2.61/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.61/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.61/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.61/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.61/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.38  
% 2.61/1.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.61/1.39  tff(f_37, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 2.61/1.39  tff(f_75, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 2.61/1.39  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.61/1.39  tff(f_60, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.61/1.39  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.61/1.39  tff(c_66, plain, (![A_33, B_34]: (r2_hidden('#skF_1'(A_33, B_34), A_33) | r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.61/1.39  tff(c_8, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.39  tff(c_81, plain, (![A_35, B_36]: (~v1_xboole_0(A_35) | r1_tarski(A_35, B_36))), inference(resolution, [status(thm)], [c_66, c_8])).
% 2.61/1.39  tff(c_32, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.61/1.39  tff(c_85, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_81, c_32])).
% 2.61/1.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.61/1.39  tff(c_451, plain, (![B_82, A_83]: (m1_subset_1(B_82, A_83) | ~r2_hidden(B_82, A_83) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.39  tff(c_470, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_451])).
% 2.61/1.39  tff(c_153, plain, (![B_45, A_46]: (m1_subset_1(B_45, A_46) | ~r2_hidden(B_45, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.39  tff(c_168, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_153])).
% 2.61/1.39  tff(c_26, plain, (![B_14, A_13]: (m1_subset_1(B_14, A_13) | ~v1_xboole_0(B_14) | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.39  tff(c_34, plain, (![D_20]: (r2_hidden(D_20, '#skF_6') | ~r2_hidden(D_20, '#skF_5') | ~m1_subset_1(D_20, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.61/1.39  tff(c_136, plain, (![B_44]: (r2_hidden('#skF_1'('#skF_5', B_44), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_5', B_44), '#skF_4') | r1_tarski('#skF_5', B_44))), inference(resolution, [status(thm)], [c_66, c_34])).
% 2.61/1.39  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.61/1.39  tff(c_140, plain, (~m1_subset_1('#skF_1'('#skF_5', '#skF_6'), '#skF_4') | r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_136, c_4])).
% 2.61/1.39  tff(c_146, plain, (~m1_subset_1('#skF_1'('#skF_5', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_140])).
% 2.61/1.39  tff(c_151, plain, (~v1_xboole_0('#skF_1'('#skF_5', '#skF_6')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_26, c_146])).
% 2.61/1.39  tff(c_152, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_151])).
% 2.61/1.39  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.61/1.39  tff(c_30, plain, (![A_15]: (~v1_xboole_0(k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.61/1.39  tff(c_86, plain, (![B_37, A_38]: (r2_hidden(B_37, A_38) | ~m1_subset_1(B_37, A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.39  tff(c_10, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.61/1.39  tff(c_94, plain, (![B_37, A_8]: (r1_tarski(B_37, A_8) | ~m1_subset_1(B_37, k1_zfmisc_1(A_8)) | v1_xboole_0(k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_86, c_10])).
% 2.61/1.39  tff(c_105, plain, (![B_39, A_40]: (r1_tarski(B_39, A_40) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)))), inference(negUnitSimplification, [status(thm)], [c_30, c_94])).
% 2.61/1.39  tff(c_117, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_105])).
% 2.61/1.39  tff(c_24, plain, (![B_14, A_13]: (r2_hidden(B_14, A_13) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.39  tff(c_181, plain, (![C_49, B_50, A_51]: (r2_hidden(C_49, B_50) | ~r2_hidden(C_49, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.61/1.39  tff(c_277, plain, (![B_68, B_69, A_70]: (r2_hidden(B_68, B_69) | ~r1_tarski(A_70, B_69) | ~m1_subset_1(B_68, A_70) | v1_xboole_0(A_70))), inference(resolution, [status(thm)], [c_24, c_181])).
% 2.61/1.39  tff(c_281, plain, (![B_68]: (r2_hidden(B_68, '#skF_4') | ~m1_subset_1(B_68, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_117, c_277])).
% 2.61/1.39  tff(c_297, plain, (![B_71]: (r2_hidden(B_71, '#skF_4') | ~m1_subset_1(B_71, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_85, c_281])).
% 2.61/1.39  tff(c_22, plain, (![B_14, A_13]: (m1_subset_1(B_14, A_13) | ~r2_hidden(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.39  tff(c_305, plain, (![B_71]: (m1_subset_1(B_71, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_71, '#skF_5'))), inference(resolution, [status(thm)], [c_297, c_22])).
% 2.61/1.39  tff(c_355, plain, (![B_74]: (m1_subset_1(B_74, '#skF_4') | ~m1_subset_1(B_74, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_152, c_305])).
% 2.61/1.39  tff(c_359, plain, (![B_2]: (m1_subset_1('#skF_1'('#skF_5', B_2), '#skF_4') | v1_xboole_0('#skF_5') | r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_168, c_355])).
% 2.61/1.39  tff(c_421, plain, (![B_80]: (m1_subset_1('#skF_1'('#skF_5', B_80), '#skF_4') | r1_tarski('#skF_5', B_80))), inference(negUnitSimplification, [status(thm)], [c_85, c_359])).
% 2.61/1.39  tff(c_428, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_421, c_146])).
% 2.61/1.39  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_428])).
% 2.61/1.39  tff(c_440, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_151])).
% 2.61/1.39  tff(c_484, plain, (![C_86, B_87, A_88]: (r2_hidden(C_86, B_87) | ~r2_hidden(C_86, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.61/1.39  tff(c_559, plain, (![B_104, B_105, A_106]: (r2_hidden(B_104, B_105) | ~r1_tarski(A_106, B_105) | ~m1_subset_1(B_104, A_106) | v1_xboole_0(A_106))), inference(resolution, [status(thm)], [c_24, c_484])).
% 2.61/1.39  tff(c_563, plain, (![B_104]: (r2_hidden(B_104, '#skF_4') | ~m1_subset_1(B_104, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_117, c_559])).
% 2.61/1.39  tff(c_592, plain, (![B_109]: (r2_hidden(B_109, '#skF_4') | ~m1_subset_1(B_109, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_85, c_563])).
% 2.61/1.39  tff(c_607, plain, (![B_109]: (~v1_xboole_0('#skF_4') | ~m1_subset_1(B_109, '#skF_5'))), inference(resolution, [status(thm)], [c_592, c_8])).
% 2.61/1.39  tff(c_616, plain, (![B_110]: (~m1_subset_1(B_110, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_440, c_607])).
% 2.61/1.39  tff(c_620, plain, (![B_2]: (v1_xboole_0('#skF_5') | r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_470, c_616])).
% 2.61/1.39  tff(c_627, plain, (![B_2]: (r1_tarski('#skF_5', B_2))), inference(negUnitSimplification, [status(thm)], [c_85, c_620])).
% 2.61/1.39  tff(c_633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_627, c_32])).
% 2.61/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.39  
% 2.61/1.39  Inference rules
% 2.61/1.39  ----------------------
% 2.61/1.39  #Ref     : 0
% 2.61/1.39  #Sup     : 117
% 2.61/1.39  #Fact    : 0
% 2.61/1.39  #Define  : 0
% 2.61/1.39  #Split   : 3
% 2.61/1.39  #Chain   : 0
% 2.61/1.39  #Close   : 0
% 2.61/1.39  
% 2.61/1.39  Ordering : KBO
% 2.61/1.39  
% 2.61/1.39  Simplification rules
% 2.61/1.39  ----------------------
% 2.61/1.39  #Subsume      : 31
% 2.61/1.39  #Demod        : 13
% 2.61/1.39  #Tautology    : 23
% 2.61/1.39  #SimpNegUnit  : 24
% 2.61/1.39  #BackRed      : 1
% 2.61/1.39  
% 2.61/1.39  #Partial instantiations: 0
% 2.61/1.39  #Strategies tried      : 1
% 2.61/1.39  
% 2.61/1.39  Timing (in seconds)
% 2.61/1.39  ----------------------
% 2.61/1.39  Preprocessing        : 0.30
% 2.61/1.39  Parsing              : 0.16
% 2.61/1.39  CNF conversion       : 0.02
% 2.61/1.39  Main loop            : 0.32
% 2.61/1.39  Inferencing          : 0.13
% 2.61/1.39  Reduction            : 0.08
% 2.61/1.40  Demodulation         : 0.05
% 2.61/1.40  BG Simplification    : 0.02
% 2.61/1.40  Subsumption          : 0.07
% 2.61/1.40  Abstraction          : 0.01
% 2.61/1.40  MUC search           : 0.00
% 2.61/1.40  Cooper               : 0.00
% 2.61/1.40  Total                : 0.65
% 2.61/1.40  Index Insertion      : 0.00
% 2.61/1.40  Index Deletion       : 0.00
% 2.61/1.40  Index Matching       : 0.00
% 2.61/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
