%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:22 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 109 expanded)
%              Number of leaves         :   26 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 232 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_61,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_8,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_69,plain,(
    ! [B_32,A_33] :
      ( v1_xboole_0(B_32)
      | ~ m1_subset_1(B_32,A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_77,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_69])).

tff(c_78,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_89,plain,(
    ! [B_38,A_39] :
      ( r2_hidden(B_38,A_39)
      | ~ m1_subset_1(B_38,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_310,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(B_65,A_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | v1_xboole_0(k1_zfmisc_1(A_66)) ) ),
    inference(resolution,[status(thm)],[c_89,c_10])).

tff(c_324,plain,
    ( r1_tarski('#skF_6','#skF_4')
    | v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_310])).

tff(c_330,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_324])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_337,plain,(
    ! [A_67] :
      ( r1_tarski(A_67,'#skF_4')
      | ~ r1_tarski(A_67,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_330,c_6])).

tff(c_362,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_337])).

tff(c_12,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_99,plain,(
    ! [B_40,A_41] :
      ( m1_subset_1(B_40,A_41)
      | ~ r2_hidden(B_40,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_110,plain,(
    ! [C_13,A_9] :
      ( m1_subset_1(C_13,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_99])).

tff(c_40,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_842,plain,(
    ! [C_94,A_95,B_96] :
      ( r1_tarski(C_94,k3_subset_1(A_95,B_96))
      | ~ r1_tarski(B_96,k3_subset_1(A_95,C_94))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(A_95))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_860,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_842])).

tff(c_876,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_860])).

tff(c_878,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_876])).

tff(c_881,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_110,c_878])).

tff(c_887,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_881])).

tff(c_889,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_887])).

tff(c_891,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_876])).

tff(c_890,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_876])).

tff(c_913,plain,(
    ! [A_97] :
      ( r1_tarski(A_97,k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_97,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_890,c_6])).

tff(c_30,plain,(
    ! [A_16] : k1_subset_1(A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [A_21,B_22] :
      ( k1_subset_1(A_21) = B_22
      | ~ r1_tarski(B_22,k3_subset_1(A_21,B_22))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_45,plain,(
    ! [B_22,A_21] :
      ( k1_xboole_0 = B_22
      | ~ r1_tarski(B_22,k3_subset_1(A_21,B_22))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_36])).

tff(c_925,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_913,c_45])).

tff(c_935,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_891,c_925])).

tff(c_937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_935])).

tff(c_939,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_940,plain,(
    ! [C_98,A_99] :
      ( r2_hidden(C_98,k1_zfmisc_1(A_99))
      | ~ r1_tarski(C_98,A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_949,plain,(
    ! [A_100,C_101] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_100))
      | ~ r1_tarski(C_101,A_100) ) ),
    inference(resolution,[status(thm)],[c_940,c_2])).

tff(c_963,plain,(
    ! [C_104] : ~ r1_tarski(C_104,'#skF_4') ),
    inference(resolution,[status(thm)],[c_939,c_949])).

tff(c_968,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_963])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:37:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.44  
% 2.69/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.44  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.69/1.44  
% 2.69/1.44  %Foreground sorts:
% 2.69/1.44  
% 2.69/1.44  
% 2.69/1.44  %Background operators:
% 2.69/1.44  
% 2.69/1.44  
% 2.69/1.44  %Foreground operators:
% 2.69/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.69/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.69/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.44  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.69/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.69/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.69/1.44  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.69/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.44  
% 2.69/1.45  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.69/1.45  tff(f_85, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 2.69/1.45  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.69/1.45  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.69/1.45  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.69/1.45  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 2.69/1.45  tff(f_61, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.69/1.45  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.69/1.45  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.69/1.45  tff(c_8, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.69/1.45  tff(c_38, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.69/1.45  tff(c_42, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.69/1.45  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.69/1.45  tff(c_69, plain, (![B_32, A_33]: (v1_xboole_0(B_32) | ~m1_subset_1(B_32, A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.69/1.45  tff(c_77, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_69])).
% 2.69/1.45  tff(c_78, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_77])).
% 2.69/1.45  tff(c_89, plain, (![B_38, A_39]: (r2_hidden(B_38, A_39) | ~m1_subset_1(B_38, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.69/1.45  tff(c_10, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.69/1.45  tff(c_310, plain, (![B_65, A_66]: (r1_tarski(B_65, A_66) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | v1_xboole_0(k1_zfmisc_1(A_66)))), inference(resolution, [status(thm)], [c_89, c_10])).
% 2.69/1.45  tff(c_324, plain, (r1_tarski('#skF_6', '#skF_4') | v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_310])).
% 2.69/1.45  tff(c_330, plain, (r1_tarski('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_78, c_324])).
% 2.69/1.45  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.69/1.45  tff(c_337, plain, (![A_67]: (r1_tarski(A_67, '#skF_4') | ~r1_tarski(A_67, '#skF_6'))), inference(resolution, [status(thm)], [c_330, c_6])).
% 2.69/1.45  tff(c_362, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_337])).
% 2.69/1.45  tff(c_12, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.69/1.45  tff(c_99, plain, (![B_40, A_41]: (m1_subset_1(B_40, A_41) | ~r2_hidden(B_40, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.69/1.45  tff(c_110, plain, (![C_13, A_9]: (m1_subset_1(C_13, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(resolution, [status(thm)], [c_12, c_99])).
% 2.69/1.45  tff(c_40, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.69/1.45  tff(c_842, plain, (![C_94, A_95, B_96]: (r1_tarski(C_94, k3_subset_1(A_95, B_96)) | ~r1_tarski(B_96, k3_subset_1(A_95, C_94)) | ~m1_subset_1(C_94, k1_zfmisc_1(A_95)) | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.69/1.45  tff(c_860, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_842])).
% 2.69/1.45  tff(c_876, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_860])).
% 2.69/1.45  tff(c_878, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_876])).
% 2.69/1.45  tff(c_881, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_110, c_878])).
% 2.69/1.45  tff(c_887, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_362, c_881])).
% 2.69/1.45  tff(c_889, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_887])).
% 2.69/1.45  tff(c_891, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_876])).
% 2.69/1.45  tff(c_890, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_876])).
% 2.69/1.45  tff(c_913, plain, (![A_97]: (r1_tarski(A_97, k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski(A_97, '#skF_6'))), inference(resolution, [status(thm)], [c_890, c_6])).
% 2.69/1.45  tff(c_30, plain, (![A_16]: (k1_subset_1(A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.69/1.45  tff(c_36, plain, (![A_21, B_22]: (k1_subset_1(A_21)=B_22 | ~r1_tarski(B_22, k3_subset_1(A_21, B_22)) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.69/1.45  tff(c_45, plain, (![B_22, A_21]: (k1_xboole_0=B_22 | ~r1_tarski(B_22, k3_subset_1(A_21, B_22)) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_36])).
% 2.69/1.45  tff(c_925, plain, (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_913, c_45])).
% 2.69/1.45  tff(c_935, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_891, c_925])).
% 2.69/1.45  tff(c_937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_935])).
% 2.69/1.45  tff(c_939, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_77])).
% 2.69/1.45  tff(c_940, plain, (![C_98, A_99]: (r2_hidden(C_98, k1_zfmisc_1(A_99)) | ~r1_tarski(C_98, A_99))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.69/1.45  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.45  tff(c_949, plain, (![A_100, C_101]: (~v1_xboole_0(k1_zfmisc_1(A_100)) | ~r1_tarski(C_101, A_100))), inference(resolution, [status(thm)], [c_940, c_2])).
% 2.69/1.45  tff(c_963, plain, (![C_104]: (~r1_tarski(C_104, '#skF_4'))), inference(resolution, [status(thm)], [c_939, c_949])).
% 2.69/1.45  tff(c_968, plain, $false, inference(resolution, [status(thm)], [c_8, c_963])).
% 2.69/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.45  
% 2.69/1.45  Inference rules
% 2.69/1.45  ----------------------
% 2.69/1.45  #Ref     : 0
% 2.69/1.45  #Sup     : 188
% 2.69/1.45  #Fact    : 0
% 2.69/1.45  #Define  : 0
% 2.69/1.45  #Split   : 9
% 2.69/1.45  #Chain   : 0
% 2.69/1.45  #Close   : 0
% 2.69/1.45  
% 2.69/1.45  Ordering : KBO
% 2.69/1.45  
% 2.69/1.45  Simplification rules
% 2.69/1.45  ----------------------
% 2.69/1.45  #Subsume      : 38
% 2.69/1.45  #Demod        : 60
% 2.69/1.45  #Tautology    : 53
% 2.69/1.45  #SimpNegUnit  : 19
% 2.69/1.45  #BackRed      : 6
% 2.69/1.45  
% 2.69/1.45  #Partial instantiations: 0
% 2.69/1.45  #Strategies tried      : 1
% 2.69/1.45  
% 2.69/1.45  Timing (in seconds)
% 2.69/1.45  ----------------------
% 2.69/1.45  Preprocessing        : 0.30
% 2.69/1.45  Parsing              : 0.16
% 2.69/1.45  CNF conversion       : 0.02
% 2.69/1.45  Main loop            : 0.38
% 2.69/1.45  Inferencing          : 0.14
% 2.69/1.45  Reduction            : 0.12
% 2.69/1.45  Demodulation         : 0.08
% 2.69/1.45  BG Simplification    : 0.02
% 2.69/1.45  Subsumption          : 0.08
% 2.69/1.46  Abstraction          : 0.02
% 2.69/1.46  MUC search           : 0.00
% 2.69/1.46  Cooper               : 0.00
% 2.69/1.46  Total                : 0.71
% 2.69/1.46  Index Insertion      : 0.00
% 2.69/1.46  Index Deletion       : 0.00
% 2.69/1.46  Index Matching       : 0.00
% 2.69/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
