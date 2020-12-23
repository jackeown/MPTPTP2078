%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:50 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 121 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  104 ( 260 expanded)
%              Number of equality atoms :   10 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

tff(c_30,plain,(
    ! [A_17] : m1_subset_1('#skF_3'(A_17),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_50,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_5')
      | ~ m1_subset_1(C_28,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( ~ v1_xboole_0(B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_54,plain,(
    ! [C_28] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_28,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_16])).

tff(c_55,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_65,plain,(
    ! [B_32,A_33] :
      ( v1_xboole_0(B_32)
      | ~ m1_subset_1(B_32,A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_68,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_65])).

tff(c_74,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_68])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_xboole_0(A_5,B_6)
      | B_6 = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( m1_subset_1(B_16,A_15)
      | ~ v1_xboole_0(B_16)
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    ! [C_20] :
      ( r2_hidden(C_20,'#skF_5')
      | ~ m1_subset_1(C_20,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_129,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden('#skF_2'(A_49,B_50),A_49)
      | ~ r2_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_174,plain,(
    ! [B_55] :
      ( ~ r2_xboole_0('#skF_5',B_55)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_55),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_129])).

tff(c_178,plain,(
    ! [B_55] :
      ( ~ r2_xboole_0('#skF_5',B_55)
      | ~ v1_xboole_0('#skF_2'('#skF_5',B_55))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_174])).

tff(c_184,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),B_8)
      | ~ r2_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_145,plain,(
    ! [B_51,A_52] :
      ( m1_subset_1(B_51,A_52)
      | ~ r2_hidden(B_51,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_222,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1('#skF_2'(A_64,B_65),B_65)
      | v1_xboole_0(B_65)
      | ~ r2_xboole_0(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_14,c_145])).

tff(c_144,plain,(
    ! [B_50] :
      ( ~ r2_xboole_0('#skF_5',B_50)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_50),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_129])).

tff(c_230,plain,
    ( v1_xboole_0('#skF_4')
    | ~ r2_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_222,c_144])).

tff(c_237,plain,(
    ~ r2_xboole_0('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_230])).

tff(c_241,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_237])).

tff(c_244,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_241])).

tff(c_88,plain,(
    ! [B_39,A_40] :
      ( r2_hidden(B_39,A_40)
      | ~ m1_subset_1(B_39,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_14] : k3_tarski(k1_zfmisc_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_61,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,k3_tarski(B_31))
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,(
    ! [A_30,A_14] :
      ( r1_tarski(A_30,A_14)
      | ~ r2_hidden(A_30,k1_zfmisc_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_61])).

tff(c_250,plain,(
    ! [B_68,A_69] :
      ( r1_tarski(B_68,A_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | v1_xboole_0(k1_zfmisc_1(A_69)) ) ),
    inference(resolution,[status(thm)],[c_88,c_64])).

tff(c_265,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_250])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_244,c_265])).

tff(c_278,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_391,plain,(
    ! [B_82,A_83] :
      ( r1_tarski(B_82,A_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_83))
      | v1_xboole_0(k1_zfmisc_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_88,c_64])).

tff(c_409,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_391])).

tff(c_422,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_409])).

tff(c_109,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_2'(A_43,B_44),B_44)
      | ~ r2_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_119,plain,(
    ! [B_45,A_46] :
      ( ~ v1_xboole_0(B_45)
      | ~ r2_xboole_0(A_46,B_45) ) ),
    inference(resolution,[status(thm)],[c_109,c_16])).

tff(c_123,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_6,c_119])).

tff(c_426,plain,
    ( ~ v1_xboole_0('#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_422,c_123])).

tff(c_429,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_426])).

tff(c_431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_429])).

tff(c_439,plain,(
    ! [C_85] : ~ m1_subset_1(C_85,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_444,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_30,c_439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:09:00 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.37  
% 2.09/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.37  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 2.09/1.37  
% 2.09/1.37  %Foreground sorts:
% 2.09/1.37  
% 2.09/1.37  
% 2.09/1.37  %Background operators:
% 2.09/1.37  
% 2.09/1.37  
% 2.09/1.37  %Foreground operators:
% 2.09/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.09/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.37  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.09/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.09/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.37  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.09/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.09/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.37  
% 2.09/1.38  tff(f_75, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.09/1.38  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 2.09/1.38  tff(f_53, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 2.09/1.38  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.09/1.38  tff(f_38, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.09/1.38  tff(f_48, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.09/1.38  tff(f_59, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.09/1.38  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 2.09/1.38  tff(c_30, plain, (![A_17]: (m1_subset_1('#skF_3'(A_17), A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.09/1.38  tff(c_32, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.09/1.38  tff(c_50, plain, (![C_28]: (r2_hidden(C_28, '#skF_5') | ~m1_subset_1(C_28, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.09/1.38  tff(c_16, plain, (![B_11, A_10]: (~v1_xboole_0(B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.38  tff(c_54, plain, (![C_28]: (~v1_xboole_0('#skF_5') | ~m1_subset_1(C_28, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_16])).
% 2.09/1.38  tff(c_55, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_54])).
% 2.09/1.38  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.09/1.38  tff(c_65, plain, (![B_32, A_33]: (v1_xboole_0(B_32) | ~m1_subset_1(B_32, A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.09/1.38  tff(c_68, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_65])).
% 2.09/1.38  tff(c_74, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_55, c_68])).
% 2.09/1.38  tff(c_6, plain, (![A_5, B_6]: (r2_xboole_0(A_5, B_6) | B_6=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.09/1.38  tff(c_26, plain, (![B_16, A_15]: (m1_subset_1(B_16, A_15) | ~v1_xboole_0(B_16) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.09/1.38  tff(c_34, plain, (![C_20]: (r2_hidden(C_20, '#skF_5') | ~m1_subset_1(C_20, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.09/1.38  tff(c_129, plain, (![A_49, B_50]: (~r2_hidden('#skF_2'(A_49, B_50), A_49) | ~r2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.09/1.38  tff(c_174, plain, (![B_55]: (~r2_xboole_0('#skF_5', B_55) | ~m1_subset_1('#skF_2'('#skF_5', B_55), '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_129])).
% 2.09/1.38  tff(c_178, plain, (![B_55]: (~r2_xboole_0('#skF_5', B_55) | ~v1_xboole_0('#skF_2'('#skF_5', B_55)) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_174])).
% 2.09/1.38  tff(c_184, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_178])).
% 2.09/1.38  tff(c_14, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), B_8) | ~r2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.09/1.38  tff(c_145, plain, (![B_51, A_52]: (m1_subset_1(B_51, A_52) | ~r2_hidden(B_51, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.09/1.38  tff(c_222, plain, (![A_64, B_65]: (m1_subset_1('#skF_2'(A_64, B_65), B_65) | v1_xboole_0(B_65) | ~r2_xboole_0(A_64, B_65))), inference(resolution, [status(thm)], [c_14, c_145])).
% 2.09/1.38  tff(c_144, plain, (![B_50]: (~r2_xboole_0('#skF_5', B_50) | ~m1_subset_1('#skF_2'('#skF_5', B_50), '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_129])).
% 2.09/1.38  tff(c_230, plain, (v1_xboole_0('#skF_4') | ~r2_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_222, c_144])).
% 2.09/1.38  tff(c_237, plain, (~r2_xboole_0('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_184, c_230])).
% 2.09/1.38  tff(c_241, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_6, c_237])).
% 2.09/1.38  tff(c_244, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_241])).
% 2.09/1.38  tff(c_88, plain, (![B_39, A_40]: (r2_hidden(B_39, A_40) | ~m1_subset_1(B_39, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.09/1.38  tff(c_20, plain, (![A_14]: (k3_tarski(k1_zfmisc_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.09/1.38  tff(c_61, plain, (![A_30, B_31]: (r1_tarski(A_30, k3_tarski(B_31)) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.09/1.38  tff(c_64, plain, (![A_30, A_14]: (r1_tarski(A_30, A_14) | ~r2_hidden(A_30, k1_zfmisc_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_61])).
% 2.09/1.38  tff(c_250, plain, (![B_68, A_69]: (r1_tarski(B_68, A_69) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | v1_xboole_0(k1_zfmisc_1(A_69)))), inference(resolution, [status(thm)], [c_88, c_64])).
% 2.09/1.38  tff(c_265, plain, (r1_tarski('#skF_5', '#skF_4') | v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_250])).
% 2.09/1.38  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_244, c_265])).
% 2.09/1.38  tff(c_278, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_178])).
% 2.09/1.38  tff(c_391, plain, (![B_82, A_83]: (r1_tarski(B_82, A_83) | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)) | v1_xboole_0(k1_zfmisc_1(A_83)))), inference(resolution, [status(thm)], [c_88, c_64])).
% 2.09/1.38  tff(c_409, plain, (r1_tarski('#skF_5', '#skF_4') | v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_391])).
% 2.09/1.39  tff(c_422, plain, (r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_409])).
% 2.09/1.39  tff(c_109, plain, (![A_43, B_44]: (r2_hidden('#skF_2'(A_43, B_44), B_44) | ~r2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.09/1.39  tff(c_119, plain, (![B_45, A_46]: (~v1_xboole_0(B_45) | ~r2_xboole_0(A_46, B_45))), inference(resolution, [status(thm)], [c_109, c_16])).
% 2.09/1.39  tff(c_123, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_6, c_119])).
% 2.09/1.39  tff(c_426, plain, (~v1_xboole_0('#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_422, c_123])).
% 2.09/1.39  tff(c_429, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_278, c_426])).
% 2.09/1.39  tff(c_431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_429])).
% 2.09/1.39  tff(c_439, plain, (![C_85]: (~m1_subset_1(C_85, '#skF_4'))), inference(splitRight, [status(thm)], [c_54])).
% 2.09/1.39  tff(c_444, plain, $false, inference(resolution, [status(thm)], [c_30, c_439])).
% 2.09/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.39  
% 2.09/1.39  Inference rules
% 2.09/1.39  ----------------------
% 2.09/1.39  #Ref     : 0
% 2.09/1.39  #Sup     : 76
% 2.09/1.39  #Fact    : 0
% 2.09/1.39  #Define  : 0
% 2.09/1.39  #Split   : 2
% 2.09/1.39  #Chain   : 0
% 2.09/1.39  #Close   : 0
% 2.09/1.39  
% 2.09/1.39  Ordering : KBO
% 2.09/1.39  
% 2.09/1.39  Simplification rules
% 2.09/1.39  ----------------------
% 2.09/1.39  #Subsume      : 19
% 2.09/1.39  #Demod        : 11
% 2.09/1.39  #Tautology    : 22
% 2.09/1.39  #SimpNegUnit  : 14
% 2.09/1.39  #BackRed      : 0
% 2.09/1.39  
% 2.09/1.39  #Partial instantiations: 0
% 2.09/1.39  #Strategies tried      : 1
% 2.09/1.39  
% 2.09/1.39  Timing (in seconds)
% 2.09/1.39  ----------------------
% 2.51/1.39  Preprocessing        : 0.31
% 2.51/1.39  Parsing              : 0.16
% 2.51/1.39  CNF conversion       : 0.02
% 2.51/1.39  Main loop            : 0.24
% 2.51/1.39  Inferencing          : 0.10
% 2.51/1.39  Reduction            : 0.06
% 2.51/1.39  Demodulation         : 0.03
% 2.51/1.39  BG Simplification    : 0.01
% 2.51/1.39  Subsumption          : 0.05
% 2.51/1.39  Abstraction          : 0.01
% 2.51/1.39  MUC search           : 0.00
% 2.51/1.39  Cooper               : 0.00
% 2.51/1.39  Total                : 0.59
% 2.51/1.39  Index Insertion      : 0.00
% 2.51/1.39  Index Deletion       : 0.00
% 2.51/1.39  Index Matching       : 0.00
% 2.51/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
