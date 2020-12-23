%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:51 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   63 (  78 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :   81 ( 142 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_71,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_50,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_98,plain,(
    ! [B_37,A_38] :
      ( v1_xboole_0(B_37)
      | ~ m1_subset_1(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_110,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_98])).

tff(c_111,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_36,plain,(
    ! [B_17,A_16] :
      ( r2_hidden(B_17,A_16)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_183,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = k3_subset_1(A_49,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_196,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_183])).

tff(c_44,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_139,plain,(
    ! [B_45,A_46] :
      ( r2_hidden(B_45,A_46)
      | ~ m1_subset_1(B_45,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_146,plain,(
    ! [B_45,A_11] :
      ( r1_tarski(B_45,A_11)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_139,c_22])).

tff(c_165,plain,(
    ! [B_47,A_48] :
      ( r1_tarski(B_47,A_48)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_146])).

tff(c_178,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_165])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_182,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_178,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_218,plain,(
    ! [A_51,B_52] : k5_xboole_0(A_51,k3_xboole_0(B_52,A_51)) = k4_xboole_0(A_51,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_112])).

tff(c_231,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_218])).

tff(c_245,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_231])).

tff(c_302,plain,(
    ! [A_62,C_63,B_64] :
      ( r2_hidden(A_62,C_63)
      | ~ r2_hidden(A_62,B_64)
      | r2_hidden(A_62,k5_xboole_0(B_64,C_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_352,plain,(
    ! [A_68] :
      ( r2_hidden(A_68,'#skF_4')
      | ~ r2_hidden(A_68,'#skF_3')
      | r2_hidden(A_68,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_302])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_358,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_352,c_46])).

tff(c_364,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_358])).

tff(c_367,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_364])).

tff(c_370,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_367])).

tff(c_372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_370])).

tff(c_374,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_396,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_374,c_4])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_396])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:43:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.26  
% 2.21/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.26  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.21/1.26  
% 2.21/1.26  %Foreground sorts:
% 2.21/1.26  
% 2.21/1.26  
% 2.21/1.26  %Background operators:
% 2.21/1.26  
% 2.21/1.26  
% 2.21/1.26  %Foreground operators:
% 2.21/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.21/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.26  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.21/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.21/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.21/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.26  
% 2.21/1.27  tff(f_86, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 2.21/1.27  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.21/1.27  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.21/1.27  tff(f_71, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.21/1.27  tff(f_51, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.21/1.27  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.21/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.21/1.27  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.21/1.27  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.21/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.21/1.27  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.27  tff(c_50, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.27  tff(c_98, plain, (![B_37, A_38]: (v1_xboole_0(B_37) | ~m1_subset_1(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.21/1.27  tff(c_110, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_98])).
% 2.21/1.27  tff(c_111, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_110])).
% 2.21/1.27  tff(c_36, plain, (![B_17, A_16]: (r2_hidden(B_17, A_16) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.21/1.27  tff(c_48, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.27  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.27  tff(c_183, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=k3_subset_1(A_49, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.21/1.27  tff(c_196, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_183])).
% 2.21/1.27  tff(c_44, plain, (![A_20]: (~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.21/1.27  tff(c_139, plain, (![B_45, A_46]: (r2_hidden(B_45, A_46) | ~m1_subset_1(B_45, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.21/1.27  tff(c_22, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.21/1.27  tff(c_146, plain, (![B_45, A_11]: (r1_tarski(B_45, A_11) | ~m1_subset_1(B_45, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_139, c_22])).
% 2.21/1.27  tff(c_165, plain, (![B_47, A_48]: (r1_tarski(B_47, A_48) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)))), inference(negUnitSimplification, [status(thm)], [c_44, c_146])).
% 2.21/1.27  tff(c_178, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_165])).
% 2.21/1.27  tff(c_20, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.21/1.27  tff(c_182, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_178, c_20])).
% 2.21/1.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.27  tff(c_112, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.21/1.27  tff(c_218, plain, (![A_51, B_52]: (k5_xboole_0(A_51, k3_xboole_0(B_52, A_51))=k4_xboole_0(A_51, B_52))), inference(superposition, [status(thm), theory('equality')], [c_2, c_112])).
% 2.21/1.27  tff(c_231, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_182, c_218])).
% 2.21/1.27  tff(c_245, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_231])).
% 2.21/1.27  tff(c_302, plain, (![A_62, C_63, B_64]: (r2_hidden(A_62, C_63) | ~r2_hidden(A_62, B_64) | r2_hidden(A_62, k5_xboole_0(B_64, C_63)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.21/1.27  tff(c_352, plain, (![A_68]: (r2_hidden(A_68, '#skF_4') | ~r2_hidden(A_68, '#skF_3') | r2_hidden(A_68, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_245, c_302])).
% 2.21/1.27  tff(c_46, plain, (~r2_hidden('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.27  tff(c_358, plain, (r2_hidden('#skF_5', '#skF_4') | ~r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_352, c_46])).
% 2.21/1.27  tff(c_364, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_358])).
% 2.21/1.27  tff(c_367, plain, (~m1_subset_1('#skF_5', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_364])).
% 2.21/1.27  tff(c_370, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_367])).
% 2.21/1.27  tff(c_372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_370])).
% 2.21/1.27  tff(c_374, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_110])).
% 2.21/1.27  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.27  tff(c_396, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_374, c_4])).
% 2.21/1.27  tff(c_400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_396])).
% 2.21/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.27  
% 2.21/1.27  Inference rules
% 2.21/1.27  ----------------------
% 2.21/1.27  #Ref     : 0
% 2.21/1.27  #Sup     : 82
% 2.21/1.27  #Fact    : 0
% 2.21/1.27  #Define  : 0
% 2.21/1.27  #Split   : 5
% 2.21/1.27  #Chain   : 0
% 2.21/1.27  #Close   : 0
% 2.21/1.27  
% 2.21/1.28  Ordering : KBO
% 2.21/1.28  
% 2.21/1.28  Simplification rules
% 2.21/1.28  ----------------------
% 2.21/1.28  #Subsume      : 4
% 2.21/1.28  #Demod        : 6
% 2.21/1.28  #Tautology    : 40
% 2.21/1.28  #SimpNegUnit  : 6
% 2.21/1.28  #BackRed      : 0
% 2.21/1.28  
% 2.21/1.28  #Partial instantiations: 0
% 2.21/1.28  #Strategies tried      : 1
% 2.21/1.28  
% 2.21/1.28  Timing (in seconds)
% 2.21/1.28  ----------------------
% 2.21/1.28  Preprocessing        : 0.31
% 2.21/1.28  Parsing              : 0.16
% 2.21/1.28  CNF conversion       : 0.02
% 2.21/1.28  Main loop            : 0.23
% 2.21/1.28  Inferencing          : 0.08
% 2.21/1.28  Reduction            : 0.07
% 2.21/1.28  Demodulation         : 0.04
% 2.21/1.28  BG Simplification    : 0.02
% 2.21/1.28  Subsumption          : 0.04
% 2.21/1.28  Abstraction          : 0.01
% 2.21/1.28  MUC search           : 0.00
% 2.21/1.28  Cooper               : 0.00
% 2.21/1.28  Total                : 0.56
% 2.21/1.28  Index Insertion      : 0.00
% 2.21/1.28  Index Deletion       : 0.00
% 2.21/1.28  Index Matching       : 0.00
% 2.21/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
