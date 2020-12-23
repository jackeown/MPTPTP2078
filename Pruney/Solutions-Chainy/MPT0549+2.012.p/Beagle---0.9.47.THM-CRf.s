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
% DateTime   : Thu Dec  3 10:00:49 EST 2020

% Result     : Theorem 6.23s
% Output     : CNFRefutation 6.55s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 140 expanded)
%              Number of leaves         :   36 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :  120 ( 233 expanded)
%              Number of equality atoms :   41 (  81 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_112,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_109,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3002,plain,(
    ! [B_294,A_295] :
      ( r1_xboole_0(k1_relat_1(B_294),A_295)
      | k7_relat_1(B_294,A_295) != k1_xboole_0
      | ~ v1_relat_1(B_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_60,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_103,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_54,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_197,plain,(
    k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_54])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1335,plain,(
    ! [B_147,A_148] :
      ( k7_relat_1(B_147,A_148) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_147),A_148)
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1365,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_1335])).

tff(c_1378,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1365])).

tff(c_40,plain,(
    ! [B_35,A_34] :
      ( k2_relat_1(k7_relat_1(B_35,A_34)) = k9_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1384,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1378,c_40])).

tff(c_1391,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_1384])).

tff(c_1393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_1391])).

tff(c_1395,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_3019,plain,
    ( k7_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3002,c_1395])).

tff(c_3036,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3019])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1472,plain,(
    ! [A_159,B_160] :
      ( r1_xboole_0(A_159,B_160)
      | k3_xboole_0(A_159,B_160) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1487,plain,(
    ! [B_160,A_159] :
      ( r1_xboole_0(B_160,A_159)
      | k3_xboole_0(A_159,B_160) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1472,c_8])).

tff(c_1510,plain,(
    ! [A_167,B_168,C_169] :
      ( ~ r1_xboole_0(A_167,B_168)
      | ~ r2_hidden(C_169,k3_xboole_0(A_167,B_168)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1560,plain,(
    ! [A_172,C_173] :
      ( ~ r1_xboole_0(A_172,A_172)
      | ~ r2_hidden(C_173,A_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1510])).

tff(c_1563,plain,(
    ! [C_173,A_159] :
      ( ~ r2_hidden(C_173,A_159)
      | k3_xboole_0(A_159,A_159) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1487,c_1560])).

tff(c_1580,plain,(
    ! [C_174,A_175] :
      ( ~ r2_hidden(C_174,A_175)
      | k1_xboole_0 != A_175 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1563])).

tff(c_1630,plain,(
    ! [B_181,A_182] :
      ( k1_xboole_0 != B_181
      | r1_xboole_0(A_182,B_181) ) ),
    inference(resolution,[status(thm)],[c_12,c_1580])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1703,plain,(
    ! [A_182] : k3_xboole_0(A_182,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1630,c_2])).

tff(c_38,plain,(
    ! [A_32,B_33] :
      ( v1_relat_1(k7_relat_1(A_32,B_33))
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3041,plain,(
    ! [C_296,D_297,A_298,B_299] :
      ( ~ r1_xboole_0(C_296,D_297)
      | r1_xboole_0(k2_zfmisc_1(A_298,C_296),k2_zfmisc_1(B_299,D_297)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    ! [A_20] :
      ( ~ r1_xboole_0(A_20,A_20)
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3077,plain,(
    ! [B_300,D_301] :
      ( k2_zfmisc_1(B_300,D_301) = k1_xboole_0
      | ~ r1_xboole_0(D_301,D_301) ) ),
    inference(resolution,[status(thm)],[c_3041,c_26])).

tff(c_3098,plain,(
    ! [B_300,A_159] :
      ( k2_zfmisc_1(B_300,A_159) = k1_xboole_0
      | k3_xboole_0(A_159,A_159) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1487,c_3077])).

tff(c_3112,plain,(
    ! [B_300] : k2_zfmisc_1(B_300,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3098])).

tff(c_1394,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1654,plain,(
    ! [B_183,A_184] :
      ( k2_relat_1(k7_relat_1(B_183,A_184)) = k9_relat_1(B_183,A_184)
      | ~ v1_relat_1(B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    ! [A_36] :
      ( r1_tarski(A_36,k2_zfmisc_1(k1_relat_1(A_36),k2_relat_1(A_36)))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_9378,plain,(
    ! [B_547,A_548] :
      ( r1_tarski(k7_relat_1(B_547,A_548),k2_zfmisc_1(k1_relat_1(k7_relat_1(B_547,A_548)),k9_relat_1(B_547,A_548)))
      | ~ v1_relat_1(k7_relat_1(B_547,A_548))
      | ~ v1_relat_1(B_547) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1654,c_42])).

tff(c_9408,plain,
    ( r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),k1_xboole_0))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1394,c_9378])).

tff(c_9423,plain,
    ( r1_tarski(k7_relat_1('#skF_4','#skF_3'),k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3112,c_9408])).

tff(c_9424,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_9423])).

tff(c_9430,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_9424])).

tff(c_9436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_9430])).

tff(c_9437,plain,(
    r1_tarski(k7_relat_1('#skF_4','#skF_3'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_9423])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9474,plain,(
    k3_xboole_0(k7_relat_1('#skF_4','#skF_3'),k1_xboole_0) = k7_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_9437,c_20])).

tff(c_9479,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1703,c_9474])).

tff(c_9481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3036,c_9479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:49:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.23/2.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.23/2.30  
% 6.23/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.23/2.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.23/2.31  
% 6.23/2.31  %Foreground sorts:
% 6.23/2.31  
% 6.23/2.31  
% 6.23/2.31  %Background operators:
% 6.23/2.31  
% 6.23/2.31  
% 6.23/2.31  %Foreground operators:
% 6.23/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.23/2.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.23/2.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.23/2.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.23/2.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.23/2.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.23/2.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.23/2.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.23/2.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.23/2.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.23/2.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.23/2.31  tff('#skF_3', type, '#skF_3': $i).
% 6.23/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.23/2.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.23/2.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.23/2.31  tff('#skF_4', type, '#skF_4': $i).
% 6.23/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.23/2.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.23/2.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.23/2.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.23/2.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.23/2.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.23/2.31  
% 6.55/2.32  tff(f_125, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 6.55/2.32  tff(f_118, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 6.55/2.32  tff(f_112, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 6.55/2.32  tff(f_105, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 6.55/2.32  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.55/2.32  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.55/2.32  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.55/2.32  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.55/2.32  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.55/2.32  tff(f_101, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 6.55/2.32  tff(f_95, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 6.55/2.32  tff(f_85, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 6.55/2.32  tff(f_109, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 6.55/2.32  tff(f_71, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.55/2.32  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.55/2.32  tff(c_3002, plain, (![B_294, A_295]: (r1_xboole_0(k1_relat_1(B_294), A_295) | k7_relat_1(B_294, A_295)!=k1_xboole_0 | ~v1_relat_1(B_294))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.55/2.32  tff(c_60, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.55/2.32  tff(c_103, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_60])).
% 6.55/2.32  tff(c_54, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.55/2.32  tff(c_197, plain, (k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_103, c_54])).
% 6.55/2.32  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.55/2.32  tff(c_1335, plain, (![B_147, A_148]: (k7_relat_1(B_147, A_148)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_147), A_148) | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.55/2.32  tff(c_1365, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_103, c_1335])).
% 6.55/2.32  tff(c_1378, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1365])).
% 6.55/2.32  tff(c_40, plain, (![B_35, A_34]: (k2_relat_1(k7_relat_1(B_35, A_34))=k9_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.55/2.32  tff(c_1384, plain, (k9_relat_1('#skF_4', '#skF_3')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1378, c_40])).
% 6.55/2.32  tff(c_1391, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_1384])).
% 6.55/2.32  tff(c_1393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_1391])).
% 6.55/2.32  tff(c_1395, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 6.55/2.32  tff(c_3019, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3002, c_1395])).
% 6.55/2.32  tff(c_3036, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3019])).
% 6.55/2.32  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.55/2.32  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.55/2.32  tff(c_1472, plain, (![A_159, B_160]: (r1_xboole_0(A_159, B_160) | k3_xboole_0(A_159, B_160)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.55/2.32  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.55/2.32  tff(c_1487, plain, (![B_160, A_159]: (r1_xboole_0(B_160, A_159) | k3_xboole_0(A_159, B_160)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1472, c_8])).
% 6.55/2.32  tff(c_1510, plain, (![A_167, B_168, C_169]: (~r1_xboole_0(A_167, B_168) | ~r2_hidden(C_169, k3_xboole_0(A_167, B_168)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.55/2.32  tff(c_1560, plain, (![A_172, C_173]: (~r1_xboole_0(A_172, A_172) | ~r2_hidden(C_173, A_172))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1510])).
% 6.55/2.32  tff(c_1563, plain, (![C_173, A_159]: (~r2_hidden(C_173, A_159) | k3_xboole_0(A_159, A_159)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1487, c_1560])).
% 6.55/2.32  tff(c_1580, plain, (![C_174, A_175]: (~r2_hidden(C_174, A_175) | k1_xboole_0!=A_175)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1563])).
% 6.55/2.32  tff(c_1630, plain, (![B_181, A_182]: (k1_xboole_0!=B_181 | r1_xboole_0(A_182, B_181))), inference(resolution, [status(thm)], [c_12, c_1580])).
% 6.55/2.32  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.55/2.32  tff(c_1703, plain, (![A_182]: (k3_xboole_0(A_182, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1630, c_2])).
% 6.55/2.32  tff(c_38, plain, (![A_32, B_33]: (v1_relat_1(k7_relat_1(A_32, B_33)) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.55/2.32  tff(c_3041, plain, (![C_296, D_297, A_298, B_299]: (~r1_xboole_0(C_296, D_297) | r1_xboole_0(k2_zfmisc_1(A_298, C_296), k2_zfmisc_1(B_299, D_297)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.55/2.32  tff(c_26, plain, (![A_20]: (~r1_xboole_0(A_20, A_20) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.55/2.32  tff(c_3077, plain, (![B_300, D_301]: (k2_zfmisc_1(B_300, D_301)=k1_xboole_0 | ~r1_xboole_0(D_301, D_301))), inference(resolution, [status(thm)], [c_3041, c_26])).
% 6.55/2.32  tff(c_3098, plain, (![B_300, A_159]: (k2_zfmisc_1(B_300, A_159)=k1_xboole_0 | k3_xboole_0(A_159, A_159)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1487, c_3077])).
% 6.55/2.32  tff(c_3112, plain, (![B_300]: (k2_zfmisc_1(B_300, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3098])).
% 6.55/2.32  tff(c_1394, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 6.55/2.32  tff(c_1654, plain, (![B_183, A_184]: (k2_relat_1(k7_relat_1(B_183, A_184))=k9_relat_1(B_183, A_184) | ~v1_relat_1(B_183))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.55/2.32  tff(c_42, plain, (![A_36]: (r1_tarski(A_36, k2_zfmisc_1(k1_relat_1(A_36), k2_relat_1(A_36))) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.55/2.32  tff(c_9378, plain, (![B_547, A_548]: (r1_tarski(k7_relat_1(B_547, A_548), k2_zfmisc_1(k1_relat_1(k7_relat_1(B_547, A_548)), k9_relat_1(B_547, A_548))) | ~v1_relat_1(k7_relat_1(B_547, A_548)) | ~v1_relat_1(B_547))), inference(superposition, [status(thm), theory('equality')], [c_1654, c_42])).
% 6.55/2.32  tff(c_9408, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), k1_xboole_0)) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1394, c_9378])).
% 6.55/2.32  tff(c_9423, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k1_xboole_0) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3112, c_9408])).
% 6.55/2.32  tff(c_9424, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_9423])).
% 6.55/2.32  tff(c_9430, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_9424])).
% 6.55/2.32  tff(c_9436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_9430])).
% 6.55/2.32  tff(c_9437, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_9423])).
% 6.55/2.32  tff(c_20, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.55/2.32  tff(c_9474, plain, (k3_xboole_0(k7_relat_1('#skF_4', '#skF_3'), k1_xboole_0)=k7_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_9437, c_20])).
% 6.55/2.32  tff(c_9479, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1703, c_9474])).
% 6.55/2.32  tff(c_9481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3036, c_9479])).
% 6.55/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.55/2.32  
% 6.55/2.32  Inference rules
% 6.55/2.32  ----------------------
% 6.55/2.32  #Ref     : 0
% 6.55/2.32  #Sup     : 2281
% 6.55/2.32  #Fact    : 0
% 6.55/2.32  #Define  : 0
% 6.55/2.32  #Split   : 8
% 6.55/2.32  #Chain   : 0
% 6.55/2.32  #Close   : 0
% 6.55/2.32  
% 6.55/2.32  Ordering : KBO
% 6.55/2.32  
% 6.55/2.32  Simplification rules
% 6.55/2.32  ----------------------
% 6.55/2.32  #Subsume      : 641
% 6.55/2.32  #Demod        : 746
% 6.55/2.32  #Tautology    : 834
% 6.55/2.32  #SimpNegUnit  : 44
% 6.55/2.32  #BackRed      : 9
% 6.55/2.32  
% 6.55/2.32  #Partial instantiations: 0
% 6.55/2.32  #Strategies tried      : 1
% 6.55/2.32  
% 6.55/2.32  Timing (in seconds)
% 6.55/2.32  ----------------------
% 6.55/2.32  Preprocessing        : 0.33
% 6.55/2.32  Parsing              : 0.18
% 6.55/2.32  CNF conversion       : 0.02
% 6.55/2.32  Main loop            : 1.23
% 6.55/2.32  Inferencing          : 0.37
% 6.55/2.32  Reduction            : 0.38
% 6.55/2.32  Demodulation         : 0.27
% 6.55/2.32  BG Simplification    : 0.04
% 6.55/2.33  Subsumption          : 0.35
% 6.55/2.33  Abstraction          : 0.06
% 6.55/2.33  MUC search           : 0.00
% 6.55/2.33  Cooper               : 0.00
% 6.55/2.33  Total                : 1.60
% 6.55/2.33  Index Insertion      : 0.00
% 6.55/2.33  Index Deletion       : 0.00
% 6.55/2.33  Index Matching       : 0.00
% 6.55/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
