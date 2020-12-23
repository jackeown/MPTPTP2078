%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:19 EST 2020

% Result     : Theorem 27.69s
% Output     : CNFRefutation 27.69s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 139 expanded)
%              Number of leaves         :   38 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  130 ( 264 expanded)
%              Number of equality atoms :   15 (  32 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_7 > #skF_1 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_6 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_140,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_101,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_125,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_99,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_130,plain,(
    v3_ordinal1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_59486,plain,(
    ! [A_168085,B_168086] :
      ( r1_ordinal1(A_168085,B_168086)
      | ~ r1_tarski(A_168085,B_168086)
      | ~ v3_ordinal1(B_168086)
      | ~ v3_ordinal1(A_168085) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_59494,plain,(
    ! [B_8] :
      ( r1_ordinal1(B_8,B_8)
      | ~ v3_ordinal1(B_8) ) ),
    inference(resolution,[status(thm)],[c_24,c_59486])).

tff(c_28,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_112,plain,(
    ! [A_57] : k2_xboole_0(A_57,k1_tarski(A_57)) = k1_ordinal1(A_57) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_402,plain,(
    ! [D_112,B_113,A_114] :
      ( ~ r2_hidden(D_112,B_113)
      | r2_hidden(D_112,k2_xboole_0(A_114,B_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1378,plain,(
    ! [D_239,A_240] :
      ( ~ r2_hidden(D_239,k1_tarski(A_240))
      | r2_hidden(D_239,k1_ordinal1(A_240)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_402])).

tff(c_1392,plain,(
    ! [C_13] : r2_hidden(C_13,k1_ordinal1(C_13)) ),
    inference(resolution,[status(thm)],[c_28,c_1378])).

tff(c_128,plain,(
    v3_ordinal1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_680,plain,(
    ! [B_141,A_142] :
      ( r2_hidden(B_141,A_142)
      | r1_ordinal1(A_142,B_141)
      | ~ v3_ordinal1(B_141)
      | ~ v3_ordinal1(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_243,plain,(
    ! [D_90,A_91,B_92] :
      ( ~ r2_hidden(D_90,A_91)
      | r2_hidden(D_90,k2_xboole_0(A_91,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_254,plain,(
    ! [D_93,A_94] :
      ( ~ r2_hidden(D_93,A_94)
      | r2_hidden(D_93,k1_ordinal1(A_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_243])).

tff(c_132,plain,
    ( ~ r1_ordinal1('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_8',k1_ordinal1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_160,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_262,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_254,c_160])).

tff(c_755,plain,
    ( r1_ordinal1('#skF_9','#skF_8')
    | ~ v3_ordinal1('#skF_8')
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_680,c_262])).

tff(c_787,plain,(
    r1_ordinal1('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_130,c_755])).

tff(c_138,plain,
    ( r2_hidden('#skF_8',k1_ordinal1('#skF_9'))
    | r1_ordinal1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_202,plain,(
    r1_ordinal1('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_138])).

tff(c_122,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,B_63)
      | ~ r1_ordinal1(A_62,B_63)
      | ~ v3_ordinal1(B_63)
      | ~ v3_ordinal1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_605,plain,(
    ! [A_135,B_136] :
      ( r1_tarski(A_135,B_136)
      | ~ r1_ordinal1(A_135,B_136)
      | ~ v3_ordinal1(B_136)
      | ~ v3_ordinal1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12944,plain,(
    ! [B_24815,A_24816] :
      ( B_24815 = A_24816
      | ~ r1_tarski(B_24815,A_24816)
      | ~ r1_ordinal1(A_24816,B_24815)
      | ~ v3_ordinal1(B_24815)
      | ~ v3_ordinal1(A_24816) ) ),
    inference(resolution,[status(thm)],[c_605,c_20])).

tff(c_59081,plain,(
    ! [B_167831,A_167832] :
      ( B_167831 = A_167832
      | ~ r1_ordinal1(B_167831,A_167832)
      | ~ r1_ordinal1(A_167832,B_167831)
      | ~ v3_ordinal1(B_167831)
      | ~ v3_ordinal1(A_167832) ) ),
    inference(resolution,[status(thm)],[c_122,c_12944])).

tff(c_59113,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r1_ordinal1('#skF_9','#skF_8')
    | ~ v3_ordinal1('#skF_8')
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_202,c_59081])).

tff(c_59134,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_130,c_787,c_59113])).

tff(c_59146,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59134,c_160])).

tff(c_59152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1392,c_59146])).

tff(c_59153,plain,(
    ~ r1_ordinal1('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_142,plain,(
    ! [A_72] :
      ( v1_ordinal1(A_72)
      | ~ v3_ordinal1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_149,plain,(
    v1_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_128,c_142])).

tff(c_59154,plain,(
    r2_hidden('#skF_8',k1_ordinal1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_60551,plain,(
    ! [D_173054,B_173055,A_173056] :
      ( r2_hidden(D_173054,B_173055)
      | r2_hidden(D_173054,A_173056)
      | ~ r2_hidden(D_173054,k2_xboole_0(A_173056,B_173055)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_69836,plain,(
    ! [D_191276,A_191277] :
      ( r2_hidden(D_191276,k1_tarski(A_191277))
      | r2_hidden(D_191276,A_191277)
      | ~ r2_hidden(D_191276,k1_ordinal1(A_191277)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_60551])).

tff(c_26,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70843,plain,(
    ! [D_191417,A_191418] :
      ( D_191417 = A_191418
      | r2_hidden(D_191417,A_191418)
      | ~ r2_hidden(D_191417,k1_ordinal1(A_191418)) ) ),
    inference(resolution,[status(thm)],[c_69836,c_26])).

tff(c_70921,plain,
    ( '#skF_9' = '#skF_8'
    | r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_59154,c_70843])).

tff(c_70922,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_70921])).

tff(c_114,plain,(
    ! [B_61,A_58] :
      ( r1_tarski(B_61,A_58)
      | ~ r2_hidden(B_61,A_58)
      | ~ v1_ordinal1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_70925,plain,
    ( r1_tarski('#skF_8','#skF_9')
    | ~ v1_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_70922,c_114])).

tff(c_70931,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_70925])).

tff(c_120,plain,(
    ! [A_62,B_63] :
      ( r1_ordinal1(A_62,B_63)
      | ~ r1_tarski(A_62,B_63)
      | ~ v3_ordinal1(B_63)
      | ~ v3_ordinal1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_70935,plain,
    ( r1_ordinal1('#skF_8','#skF_9')
    | ~ v3_ordinal1('#skF_9')
    | ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70931,c_120])).

tff(c_70940,plain,(
    r1_ordinal1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_128,c_70935])).

tff(c_70942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59153,c_70940])).

tff(c_70943,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_70921])).

tff(c_70950,plain,(
    ~ r1_ordinal1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70943,c_59153])).

tff(c_70975,plain,(
    ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_59494,c_70950])).

tff(c_70979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_70975])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.69/15.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.69/15.85  
% 27.69/15.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.69/15.85  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_7 > #skF_1 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_6 > #skF_5 > #skF_4
% 27.69/15.85  
% 27.69/15.85  %Foreground sorts:
% 27.69/15.85  
% 27.69/15.85  
% 27.69/15.85  %Background operators:
% 27.69/15.85  
% 27.69/15.85  
% 27.69/15.85  %Foreground operators:
% 27.69/15.85  tff('#skF_7', type, '#skF_7': $i > $i).
% 27.69/15.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 27.69/15.85  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 27.69/15.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.69/15.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.69/15.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 27.69/15.85  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 27.69/15.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 27.69/15.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 27.69/15.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.69/15.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 27.69/15.85  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 27.69/15.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 27.69/15.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 27.69/15.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 27.69/15.85  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 27.69/15.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 27.69/15.85  tff('#skF_9', type, '#skF_9': $i).
% 27.69/15.85  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 27.69/15.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 27.69/15.85  tff('#skF_8', type, '#skF_8': $i).
% 27.69/15.85  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 27.69/15.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.69/15.85  tff(k3_tarski, type, k3_tarski: $i > $i).
% 27.69/15.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.69/15.85  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 27.69/15.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 27.69/15.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 27.69/15.85  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 27.69/15.85  
% 27.69/15.87  tff(f_140, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 27.69/15.87  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 27.69/15.87  tff(f_116, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 27.69/15.87  tff(f_47, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 27.69/15.87  tff(f_101, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 27.69/15.87  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 27.69/15.87  tff(f_125, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 27.69/15.87  tff(f_99, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 27.69/15.87  tff(f_108, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 27.69/15.87  tff(c_130, plain, (v3_ordinal1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_140])).
% 27.69/15.87  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 27.69/15.87  tff(c_59486, plain, (![A_168085, B_168086]: (r1_ordinal1(A_168085, B_168086) | ~r1_tarski(A_168085, B_168086) | ~v3_ordinal1(B_168086) | ~v3_ordinal1(A_168085))), inference(cnfTransformation, [status(thm)], [f_116])).
% 27.69/15.87  tff(c_59494, plain, (![B_8]: (r1_ordinal1(B_8, B_8) | ~v3_ordinal1(B_8))), inference(resolution, [status(thm)], [c_24, c_59486])).
% 27.69/15.87  tff(c_28, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 27.69/15.87  tff(c_112, plain, (![A_57]: (k2_xboole_0(A_57, k1_tarski(A_57))=k1_ordinal1(A_57))), inference(cnfTransformation, [status(thm)], [f_101])).
% 27.69/15.87  tff(c_402, plain, (![D_112, B_113, A_114]: (~r2_hidden(D_112, B_113) | r2_hidden(D_112, k2_xboole_0(A_114, B_113)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 27.69/15.87  tff(c_1378, plain, (![D_239, A_240]: (~r2_hidden(D_239, k1_tarski(A_240)) | r2_hidden(D_239, k1_ordinal1(A_240)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_402])).
% 27.69/15.87  tff(c_1392, plain, (![C_13]: (r2_hidden(C_13, k1_ordinal1(C_13)))), inference(resolution, [status(thm)], [c_28, c_1378])).
% 27.69/15.87  tff(c_128, plain, (v3_ordinal1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_140])).
% 27.69/15.87  tff(c_680, plain, (![B_141, A_142]: (r2_hidden(B_141, A_142) | r1_ordinal1(A_142, B_141) | ~v3_ordinal1(B_141) | ~v3_ordinal1(A_142))), inference(cnfTransformation, [status(thm)], [f_125])).
% 27.69/15.87  tff(c_243, plain, (![D_90, A_91, B_92]: (~r2_hidden(D_90, A_91) | r2_hidden(D_90, k2_xboole_0(A_91, B_92)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 27.69/15.87  tff(c_254, plain, (![D_93, A_94]: (~r2_hidden(D_93, A_94) | r2_hidden(D_93, k1_ordinal1(A_94)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_243])).
% 27.69/15.87  tff(c_132, plain, (~r1_ordinal1('#skF_8', '#skF_9') | ~r2_hidden('#skF_8', k1_ordinal1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 27.69/15.87  tff(c_160, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_9'))), inference(splitLeft, [status(thm)], [c_132])).
% 27.69/15.87  tff(c_262, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_254, c_160])).
% 27.69/15.87  tff(c_755, plain, (r1_ordinal1('#skF_9', '#skF_8') | ~v3_ordinal1('#skF_8') | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_680, c_262])).
% 27.69/15.87  tff(c_787, plain, (r1_ordinal1('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_130, c_755])).
% 27.69/15.87  tff(c_138, plain, (r2_hidden('#skF_8', k1_ordinal1('#skF_9')) | r1_ordinal1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_140])).
% 27.69/15.87  tff(c_202, plain, (r1_ordinal1('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_160, c_138])).
% 27.69/15.87  tff(c_122, plain, (![A_62, B_63]: (r1_tarski(A_62, B_63) | ~r1_ordinal1(A_62, B_63) | ~v3_ordinal1(B_63) | ~v3_ordinal1(A_62))), inference(cnfTransformation, [status(thm)], [f_116])).
% 27.69/15.87  tff(c_605, plain, (![A_135, B_136]: (r1_tarski(A_135, B_136) | ~r1_ordinal1(A_135, B_136) | ~v3_ordinal1(B_136) | ~v3_ordinal1(A_135))), inference(cnfTransformation, [status(thm)], [f_116])).
% 27.69/15.87  tff(c_20, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 27.69/15.87  tff(c_12944, plain, (![B_24815, A_24816]: (B_24815=A_24816 | ~r1_tarski(B_24815, A_24816) | ~r1_ordinal1(A_24816, B_24815) | ~v3_ordinal1(B_24815) | ~v3_ordinal1(A_24816))), inference(resolution, [status(thm)], [c_605, c_20])).
% 27.69/15.87  tff(c_59081, plain, (![B_167831, A_167832]: (B_167831=A_167832 | ~r1_ordinal1(B_167831, A_167832) | ~r1_ordinal1(A_167832, B_167831) | ~v3_ordinal1(B_167831) | ~v3_ordinal1(A_167832))), inference(resolution, [status(thm)], [c_122, c_12944])).
% 27.69/15.87  tff(c_59113, plain, ('#skF_9'='#skF_8' | ~r1_ordinal1('#skF_9', '#skF_8') | ~v3_ordinal1('#skF_8') | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_202, c_59081])).
% 27.69/15.87  tff(c_59134, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_130, c_787, c_59113])).
% 27.69/15.87  tff(c_59146, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_59134, c_160])).
% 27.69/15.87  tff(c_59152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1392, c_59146])).
% 27.69/15.87  tff(c_59153, plain, (~r1_ordinal1('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_132])).
% 27.69/15.87  tff(c_142, plain, (![A_72]: (v1_ordinal1(A_72) | ~v3_ordinal1(A_72))), inference(cnfTransformation, [status(thm)], [f_99])).
% 27.69/15.87  tff(c_149, plain, (v1_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_128, c_142])).
% 27.69/15.87  tff(c_59154, plain, (r2_hidden('#skF_8', k1_ordinal1('#skF_9'))), inference(splitRight, [status(thm)], [c_132])).
% 27.69/15.87  tff(c_60551, plain, (![D_173054, B_173055, A_173056]: (r2_hidden(D_173054, B_173055) | r2_hidden(D_173054, A_173056) | ~r2_hidden(D_173054, k2_xboole_0(A_173056, B_173055)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 27.69/15.87  tff(c_69836, plain, (![D_191276, A_191277]: (r2_hidden(D_191276, k1_tarski(A_191277)) | r2_hidden(D_191276, A_191277) | ~r2_hidden(D_191276, k1_ordinal1(A_191277)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_60551])).
% 27.69/15.87  tff(c_26, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 27.69/15.87  tff(c_70843, plain, (![D_191417, A_191418]: (D_191417=A_191418 | r2_hidden(D_191417, A_191418) | ~r2_hidden(D_191417, k1_ordinal1(A_191418)))), inference(resolution, [status(thm)], [c_69836, c_26])).
% 27.69/15.87  tff(c_70921, plain, ('#skF_9'='#skF_8' | r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_59154, c_70843])).
% 27.69/15.87  tff(c_70922, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_70921])).
% 27.69/15.87  tff(c_114, plain, (![B_61, A_58]: (r1_tarski(B_61, A_58) | ~r2_hidden(B_61, A_58) | ~v1_ordinal1(A_58))), inference(cnfTransformation, [status(thm)], [f_108])).
% 27.69/15.87  tff(c_70925, plain, (r1_tarski('#skF_8', '#skF_9') | ~v1_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_70922, c_114])).
% 27.69/15.87  tff(c_70931, plain, (r1_tarski('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_70925])).
% 27.69/15.87  tff(c_120, plain, (![A_62, B_63]: (r1_ordinal1(A_62, B_63) | ~r1_tarski(A_62, B_63) | ~v3_ordinal1(B_63) | ~v3_ordinal1(A_62))), inference(cnfTransformation, [status(thm)], [f_116])).
% 27.69/15.87  tff(c_70935, plain, (r1_ordinal1('#skF_8', '#skF_9') | ~v3_ordinal1('#skF_9') | ~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_70931, c_120])).
% 27.69/15.87  tff(c_70940, plain, (r1_ordinal1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_128, c_70935])).
% 27.69/15.87  tff(c_70942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59153, c_70940])).
% 27.69/15.87  tff(c_70943, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_70921])).
% 27.69/15.87  tff(c_70950, plain, (~r1_ordinal1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70943, c_59153])).
% 27.69/15.87  tff(c_70975, plain, (~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_59494, c_70950])).
% 27.69/15.87  tff(c_70979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_70975])).
% 27.69/15.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.69/15.87  
% 27.69/15.87  Inference rules
% 27.69/15.87  ----------------------
% 27.69/15.87  #Ref     : 0
% 27.69/15.87  #Sup     : 12707
% 27.69/15.87  #Fact    : 54
% 27.69/15.87  #Define  : 0
% 27.69/15.87  #Split   : 8
% 27.69/15.87  #Chain   : 0
% 27.69/15.87  #Close   : 0
% 27.69/15.87  
% 27.69/15.87  Ordering : KBO
% 27.69/15.87  
% 27.69/15.87  Simplification rules
% 27.69/15.87  ----------------------
% 27.69/15.87  #Subsume      : 4272
% 27.69/15.87  #Demod        : 1925
% 27.69/15.87  #Tautology    : 390
% 27.69/15.87  #SimpNegUnit  : 183
% 27.69/15.87  #BackRed      : 129
% 27.69/15.87  
% 27.69/15.87  #Partial instantiations: 42316
% 27.69/15.87  #Strategies tried      : 1
% 27.69/15.87  
% 27.69/15.87  Timing (in seconds)
% 27.69/15.87  ----------------------
% 27.69/15.87  Preprocessing        : 0.40
% 27.69/15.87  Parsing              : 0.19
% 27.69/15.87  CNF conversion       : 0.03
% 27.69/15.87  Main loop            : 14.71
% 27.69/15.87  Inferencing          : 3.01
% 27.69/15.87  Reduction            : 4.96
% 27.69/15.87  Demodulation         : 2.35
% 27.69/15.87  BG Simplification    : 0.26
% 27.69/15.87  Subsumption          : 5.52
% 27.69/15.87  Abstraction          : 0.47
% 27.69/15.87  MUC search           : 0.00
% 27.69/15.87  Cooper               : 0.00
% 27.69/15.87  Total                : 15.14
% 27.69/15.87  Index Insertion      : 0.00
% 27.69/15.87  Index Deletion       : 0.00
% 27.69/15.87  Index Matching       : 0.00
% 27.69/15.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
