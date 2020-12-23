%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:37 EST 2020

% Result     : Theorem 28.58s
% Output     : CNFRefutation 28.58s
% Verified   : 
% Statistics : Number of formulae       :   64 (  78 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   90 ( 134 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_6 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_97,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_60,plain,(
    ! [A_33] : ~ v1_xboole_0(k1_zfmisc_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_84582,plain,(
    ! [B_1521,A_1522] :
      ( r2_hidden(B_1521,A_1522)
      | ~ m1_subset_1(B_1521,A_1522)
      | v1_xboole_0(A_1522) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_38,plain,(
    ! [C_28,A_24] :
      ( r1_tarski(C_28,A_24)
      | ~ r2_hidden(C_28,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_84598,plain,(
    ! [B_1521,A_24] :
      ( r1_tarski(B_1521,A_24)
      | ~ m1_subset_1(B_1521,k1_zfmisc_1(A_24))
      | v1_xboole_0(k1_zfmisc_1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_84582,c_38])).

tff(c_84605,plain,(
    ! [B_1523,A_1524] :
      ( r1_tarski(B_1523,A_1524)
      | ~ m1_subset_1(B_1523,k1_zfmisc_1(A_1524)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_84598])).

tff(c_84618,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_84605])).

tff(c_72,plain,
    ( r1_xboole_0('#skF_8','#skF_9')
    | r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_106,plain,(
    r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_66,plain,
    ( ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_9'))
    | ~ r1_xboole_0('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_209,plain,(
    ~ r1_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_66])).

tff(c_62,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_254,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_270,plain,(
    k4_xboole_0('#skF_7','#skF_9') = k3_subset_1('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_254])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13),B_13)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13),A_12)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_237,plain,(
    ! [C_69,B_70,A_71] :
      ( r2_hidden(C_69,B_70)
      | ~ r2_hidden(C_69,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_673,plain,(
    ! [A_117,B_118,B_119] :
      ( r2_hidden('#skF_4'(A_117,B_118),B_119)
      | ~ r1_tarski(A_117,B_119)
      | r1_xboole_0(A_117,B_118) ) ),
    inference(resolution,[status(thm)],[c_30,c_237])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_49616,plain,(
    ! [A_1160,B_1161,B_1162,A_1163] :
      ( ~ r2_hidden('#skF_4'(A_1160,B_1161),B_1162)
      | ~ r1_tarski(A_1160,k4_xboole_0(A_1163,B_1162))
      | r1_xboole_0(A_1160,B_1161) ) ),
    inference(resolution,[status(thm)],[c_673,c_10])).

tff(c_82900,plain,(
    ! [A_1500,A_1501,B_1502] :
      ( ~ r1_tarski(A_1500,k4_xboole_0(A_1501,B_1502))
      | r1_xboole_0(A_1500,B_1502) ) ),
    inference(resolution,[status(thm)],[c_28,c_49616])).

tff(c_84289,plain,(
    ! [A_1514] :
      ( ~ r1_tarski(A_1514,k3_subset_1('#skF_7','#skF_9'))
      | r1_xboole_0(A_1514,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_82900])).

tff(c_84488,plain,(
    r1_xboole_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_106,c_84289])).

tff(c_84559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_84488])).

tff(c_84560,plain,(
    r1_xboole_0('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_84820,plain,(
    ! [A_1551,B_1552] :
      ( k4_xboole_0(A_1551,B_1552) = k3_subset_1(A_1551,B_1552)
      | ~ m1_subset_1(B_1552,k1_zfmisc_1(A_1551)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_84836,plain,(
    k4_xboole_0('#skF_7','#skF_9') = k3_subset_1('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_84820])).

tff(c_85109,plain,(
    ! [A_1572,B_1573,C_1574] :
      ( r1_tarski(A_1572,k4_xboole_0(B_1573,C_1574))
      | ~ r1_xboole_0(A_1572,C_1574)
      | ~ r1_tarski(A_1572,B_1573) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_85480,plain,(
    ! [A_1606] :
      ( r1_tarski(A_1606,k3_subset_1('#skF_7','#skF_9'))
      | ~ r1_xboole_0(A_1606,'#skF_9')
      | ~ r1_tarski(A_1606,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84836,c_85109])).

tff(c_84561,plain,(
    ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_85499,plain,
    ( ~ r1_xboole_0('#skF_8','#skF_9')
    | ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_85480,c_84561])).

tff(c_85508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84618,c_84560,c_85499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.58/17.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.58/17.69  
% 28.58/17.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.58/17.69  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_6 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 28.58/17.69  
% 28.58/17.69  %Foreground sorts:
% 28.58/17.69  
% 28.58/17.69  
% 28.58/17.69  %Background operators:
% 28.58/17.69  
% 28.58/17.69  
% 28.58/17.69  %Foreground operators:
% 28.58/17.69  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 28.58/17.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.58/17.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 28.58/17.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 28.58/17.69  tff('#skF_7', type, '#skF_7': $i).
% 28.58/17.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 28.58/17.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 28.58/17.69  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 28.58/17.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 28.58/17.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 28.58/17.69  tff('#skF_9', type, '#skF_9': $i).
% 28.58/17.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 28.58/17.69  tff('#skF_8', type, '#skF_8': $i).
% 28.58/17.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.58/17.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 28.58/17.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.58/17.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 28.58/17.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 28.58/17.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 28.58/17.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 28.58/17.69  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 28.58/17.69  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 28.58/17.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 28.58/17.69  
% 28.58/17.70  tff(f_107, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 28.58/17.70  tff(f_97, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 28.58/17.70  tff(f_90, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 28.58/17.70  tff(f_77, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 28.58/17.70  tff(f_94, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 28.58/17.70  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 28.58/17.70  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 28.58/17.70  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 28.58/17.70  tff(f_68, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 28.58/17.70  tff(c_64, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 28.58/17.70  tff(c_60, plain, (![A_33]: (~v1_xboole_0(k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 28.58/17.70  tff(c_84582, plain, (![B_1521, A_1522]: (r2_hidden(B_1521, A_1522) | ~m1_subset_1(B_1521, A_1522) | v1_xboole_0(A_1522))), inference(cnfTransformation, [status(thm)], [f_90])).
% 28.58/17.70  tff(c_38, plain, (![C_28, A_24]: (r1_tarski(C_28, A_24) | ~r2_hidden(C_28, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 28.58/17.70  tff(c_84598, plain, (![B_1521, A_24]: (r1_tarski(B_1521, A_24) | ~m1_subset_1(B_1521, k1_zfmisc_1(A_24)) | v1_xboole_0(k1_zfmisc_1(A_24)))), inference(resolution, [status(thm)], [c_84582, c_38])).
% 28.58/17.70  tff(c_84605, plain, (![B_1523, A_1524]: (r1_tarski(B_1523, A_1524) | ~m1_subset_1(B_1523, k1_zfmisc_1(A_1524)))), inference(negUnitSimplification, [status(thm)], [c_60, c_84598])).
% 28.58/17.70  tff(c_84618, plain, (r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_84605])).
% 28.58/17.70  tff(c_72, plain, (r1_xboole_0('#skF_8', '#skF_9') | r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 28.58/17.70  tff(c_106, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_72])).
% 28.58/17.70  tff(c_66, plain, (~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_9')) | ~r1_xboole_0('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_107])).
% 28.58/17.70  tff(c_209, plain, (~r1_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_66])).
% 28.58/17.70  tff(c_62, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 28.58/17.70  tff(c_254, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 28.58/17.70  tff(c_270, plain, (k4_xboole_0('#skF_7', '#skF_9')=k3_subset_1('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_62, c_254])).
% 28.58/17.70  tff(c_28, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13), B_13) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 28.58/17.70  tff(c_30, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13), A_12) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 28.58/17.70  tff(c_237, plain, (![C_69, B_70, A_71]: (r2_hidden(C_69, B_70) | ~r2_hidden(C_69, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_32])).
% 28.58/17.70  tff(c_673, plain, (![A_117, B_118, B_119]: (r2_hidden('#skF_4'(A_117, B_118), B_119) | ~r1_tarski(A_117, B_119) | r1_xboole_0(A_117, B_118))), inference(resolution, [status(thm)], [c_30, c_237])).
% 28.58/17.70  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 28.58/17.70  tff(c_49616, plain, (![A_1160, B_1161, B_1162, A_1163]: (~r2_hidden('#skF_4'(A_1160, B_1161), B_1162) | ~r1_tarski(A_1160, k4_xboole_0(A_1163, B_1162)) | r1_xboole_0(A_1160, B_1161))), inference(resolution, [status(thm)], [c_673, c_10])).
% 28.58/17.70  tff(c_82900, plain, (![A_1500, A_1501, B_1502]: (~r1_tarski(A_1500, k4_xboole_0(A_1501, B_1502)) | r1_xboole_0(A_1500, B_1502))), inference(resolution, [status(thm)], [c_28, c_49616])).
% 28.58/17.70  tff(c_84289, plain, (![A_1514]: (~r1_tarski(A_1514, k3_subset_1('#skF_7', '#skF_9')) | r1_xboole_0(A_1514, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_82900])).
% 28.58/17.70  tff(c_84488, plain, (r1_xboole_0('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_106, c_84289])).
% 28.58/17.70  tff(c_84559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_84488])).
% 28.58/17.70  tff(c_84560, plain, (r1_xboole_0('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_72])).
% 28.58/17.70  tff(c_84820, plain, (![A_1551, B_1552]: (k4_xboole_0(A_1551, B_1552)=k3_subset_1(A_1551, B_1552) | ~m1_subset_1(B_1552, k1_zfmisc_1(A_1551)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 28.58/17.70  tff(c_84836, plain, (k4_xboole_0('#skF_7', '#skF_9')=k3_subset_1('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_62, c_84820])).
% 28.58/17.70  tff(c_85109, plain, (![A_1572, B_1573, C_1574]: (r1_tarski(A_1572, k4_xboole_0(B_1573, C_1574)) | ~r1_xboole_0(A_1572, C_1574) | ~r1_tarski(A_1572, B_1573))), inference(cnfTransformation, [status(thm)], [f_68])).
% 28.58/17.70  tff(c_85480, plain, (![A_1606]: (r1_tarski(A_1606, k3_subset_1('#skF_7', '#skF_9')) | ~r1_xboole_0(A_1606, '#skF_9') | ~r1_tarski(A_1606, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_84836, c_85109])).
% 28.58/17.70  tff(c_84561, plain, (~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_72])).
% 28.58/17.70  tff(c_85499, plain, (~r1_xboole_0('#skF_8', '#skF_9') | ~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_85480, c_84561])).
% 28.58/17.70  tff(c_85508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84618, c_84560, c_85499])).
% 28.58/17.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.58/17.70  
% 28.58/17.70  Inference rules
% 28.58/17.70  ----------------------
% 28.58/17.70  #Ref     : 0
% 28.58/17.70  #Sup     : 21325
% 28.58/17.70  #Fact    : 0
% 28.58/17.70  #Define  : 0
% 28.58/17.70  #Split   : 36
% 28.58/17.70  #Chain   : 0
% 28.58/17.70  #Close   : 0
% 28.58/17.70  
% 28.58/17.70  Ordering : KBO
% 28.58/17.70  
% 28.58/17.70  Simplification rules
% 28.58/17.70  ----------------------
% 28.58/17.70  #Subsume      : 4471
% 28.58/17.70  #Demod        : 10866
% 28.58/17.70  #Tautology    : 5124
% 28.58/17.70  #SimpNegUnit  : 980
% 28.58/17.70  #BackRed      : 58
% 28.58/17.70  
% 28.58/17.70  #Partial instantiations: 0
% 28.58/17.70  #Strategies tried      : 1
% 28.58/17.70  
% 28.58/17.70  Timing (in seconds)
% 28.58/17.70  ----------------------
% 28.58/17.70  Preprocessing        : 0.33
% 28.58/17.70  Parsing              : 0.17
% 28.58/17.70  CNF conversion       : 0.03
% 28.58/17.70  Main loop            : 16.62
% 28.58/17.70  Inferencing          : 2.10
% 28.58/17.70  Reduction            : 7.60
% 28.58/17.71  Demodulation         : 6.10
% 28.58/17.71  BG Simplification    : 0.26
% 28.58/17.71  Subsumption          : 5.40
% 28.58/17.71  Abstraction          : 0.37
% 28.58/17.71  MUC search           : 0.00
% 28.58/17.71  Cooper               : 0.00
% 28.58/17.71  Total                : 16.98
% 28.58/17.71  Index Insertion      : 0.00
% 28.58/17.71  Index Deletion       : 0.00
% 28.58/17.71  Index Matching       : 0.00
% 28.58/17.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
