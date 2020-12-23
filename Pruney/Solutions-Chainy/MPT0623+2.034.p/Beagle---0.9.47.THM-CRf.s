%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:10 EST 2020

% Result     : Theorem 9.01s
% Output     : CNFRefutation 9.40s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 412 expanded)
%              Number of leaves         :   36 ( 153 expanded)
%              Depth                    :   18
%              Number of atoms          :  222 (1112 expanded)
%              Number of equality atoms :  106 ( 523 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_8 > #skF_10 > #skF_2 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_79,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_110,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_92,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_50,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_62,plain,(
    ! [A_25] : v1_relat_1('#skF_8'(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_60,plain,(
    ! [A_25] : v1_funct_1('#skF_8'(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_58,plain,(
    ! [A_25] : k1_relat_1('#skF_8'(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_74,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_95,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_66,plain,(
    ! [A_31,B_35] :
      ( k1_relat_1('#skF_9'(A_31,B_35)) = A_31
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_68,plain,(
    ! [A_31,B_35] :
      ( v1_funct_1('#skF_9'(A_31,B_35))
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_70,plain,(
    ! [A_31,B_35] :
      ( v1_relat_1('#skF_9'(A_31,B_35))
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_154,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_1'(A_67,B_68),A_67)
      | r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_169,plain,(
    ! [A_17,B_68] :
      ( '#skF_1'(k1_tarski(A_17),B_68) = A_17
      | r1_tarski(k1_tarski(A_17),B_68) ) ),
    inference(resolution,[status(thm)],[c_154,c_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_229,plain,(
    ! [C_80,B_81,A_82] :
      ( r2_hidden(C_80,B_81)
      | ~ r2_hidden(C_80,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_623,plain,(
    ! [A_1184,B_1185,B_1186] :
      ( r2_hidden('#skF_1'(A_1184,B_1185),B_1186)
      | ~ r1_tarski(A_1184,B_1186)
      | r1_tarski(A_1184,B_1185) ) ),
    inference(resolution,[status(thm)],[c_6,c_229])).

tff(c_34,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_214,plain,(
    ! [D_75,A_76,B_77] :
      ( r2_hidden(D_75,A_76)
      | ~ r2_hidden(D_75,k3_xboole_0(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_221,plain,(
    ! [D_75,A_15] :
      ( r2_hidden(D_75,A_15)
      | ~ r2_hidden(D_75,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_214])).

tff(c_741,plain,(
    ! [A_1369,B_1370,A_1371] :
      ( r2_hidden('#skF_1'(A_1369,B_1370),A_1371)
      | ~ r1_tarski(A_1369,k1_xboole_0)
      | r1_tarski(A_1369,B_1370) ) ),
    inference(resolution,[status(thm)],[c_623,c_221])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_773,plain,(
    ! [A_1401,A_1402] :
      ( ~ r1_tarski(A_1401,k1_xboole_0)
      | r1_tarski(A_1401,A_1402) ) ),
    inference(resolution,[status(thm)],[c_741,c_4])).

tff(c_788,plain,(
    ! [A_1432,A_1433] :
      ( r1_tarski(k1_tarski(A_1432),A_1433)
      | '#skF_1'(k1_tarski(A_1432),k1_xboole_0) = A_1432 ) ),
    inference(resolution,[status(thm)],[c_169,c_773])).

tff(c_40,plain,(
    ! [C_21] : r2_hidden(C_21,k1_tarski(C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_235,plain,(
    ! [C_21,B_81] :
      ( r2_hidden(C_21,B_81)
      | ~ r1_tarski(k1_tarski(C_21),B_81) ) ),
    inference(resolution,[status(thm)],[c_40,c_229])).

tff(c_897,plain,(
    ! [A_1494,A_1495] :
      ( r2_hidden(A_1494,A_1495)
      | '#skF_1'(k1_tarski(A_1494),k1_xboole_0) = A_1494 ) ),
    inference(resolution,[status(thm)],[c_788,c_235])).

tff(c_996,plain,(
    ! [A_17,A_1494] :
      ( A_17 = A_1494
      | '#skF_1'(k1_tarski(A_1494),k1_xboole_0) = A_1494 ) ),
    inference(resolution,[status(thm)],[c_897,c_38])).

tff(c_8280,plain,(
    ! [A_4282] : '#skF_1'(k1_tarski(A_4282),k1_xboole_0) = A_4282 ),
    inference(factorization,[status(thm),theory(equality)],[c_996])).

tff(c_8462,plain,(
    ! [A_4374] :
      ( ~ r2_hidden(A_4374,k1_xboole_0)
      | r1_tarski(k1_tarski(A_4374),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8280,c_4])).

tff(c_770,plain,(
    ! [A_1369,A_1371] :
      ( ~ r1_tarski(A_1369,k1_xboole_0)
      | r1_tarski(A_1369,A_1371) ) ),
    inference(resolution,[status(thm)],[c_741,c_4])).

tff(c_8519,plain,(
    ! [A_4404,A_4405] :
      ( r1_tarski(k1_tarski(A_4404),A_4405)
      | ~ r2_hidden(A_4404,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8462,c_770])).

tff(c_129,plain,(
    ! [A_59,B_60] :
      ( k2_relat_1('#skF_9'(A_59,B_60)) = k1_tarski(B_60)
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_72,plain,(
    ! [C_38] :
      ( ~ r1_tarski(k2_relat_1(C_38),'#skF_10')
      | k1_relat_1(C_38) != '#skF_11'
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_135,plain,(
    ! [B_60,A_59] :
      ( ~ r1_tarski(k1_tarski(B_60),'#skF_10')
      | k1_relat_1('#skF_9'(A_59,B_60)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_59,B_60))
      | ~ v1_relat_1('#skF_9'(A_59,B_60))
      | k1_xboole_0 = A_59 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_72])).

tff(c_8637,plain,(
    ! [A_4466,A_4467] :
      ( k1_relat_1('#skF_9'(A_4466,A_4467)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_4466,A_4467))
      | ~ v1_relat_1('#skF_9'(A_4466,A_4467))
      | k1_xboole_0 = A_4466
      | ~ r2_hidden(A_4467,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8519,c_135])).

tff(c_20704,plain,(
    ! [A_13248,B_13249] :
      ( k1_relat_1('#skF_9'(A_13248,B_13249)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_13248,B_13249))
      | ~ r2_hidden(B_13249,k1_xboole_0)
      | k1_xboole_0 = A_13248 ) ),
    inference(resolution,[status(thm)],[c_70,c_8637])).

tff(c_20710,plain,(
    ! [A_13279,B_13280] :
      ( k1_relat_1('#skF_9'(A_13279,B_13280)) != '#skF_11'
      | ~ r2_hidden(B_13280,k1_xboole_0)
      | k1_xboole_0 = A_13279 ) ),
    inference(resolution,[status(thm)],[c_68,c_20704])).

tff(c_20715,plain,(
    ! [A_31,B_35] :
      ( A_31 != '#skF_11'
      | ~ r2_hidden(B_35,k1_xboole_0)
      | k1_xboole_0 = A_31
      | k1_xboole_0 = A_31 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_20710])).

tff(c_20716,plain,(
    ! [B_35] : ~ r2_hidden(B_35,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_20715])).

tff(c_8363,plain,(
    ! [A_4312,B_4313] :
      ( r2_hidden('#skF_4'(A_4312,B_4313),B_4313)
      | r2_hidden('#skF_5'(A_4312,B_4313),A_4312)
      | B_4313 = A_4312 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24142,plain,(
    ! [A_14949,A_14950,B_14951] :
      ( r2_hidden('#skF_4'(A_14949,k3_xboole_0(A_14950,B_14951)),B_14951)
      | r2_hidden('#skF_5'(A_14949,k3_xboole_0(A_14950,B_14951)),A_14949)
      | k3_xboole_0(A_14950,B_14951) = A_14949 ) ),
    inference(resolution,[status(thm)],[c_8363,c_10])).

tff(c_24214,plain,(
    ! [A_14949,A_15] :
      ( r2_hidden('#skF_4'(A_14949,k3_xboole_0(A_15,k1_xboole_0)),k1_xboole_0)
      | r2_hidden('#skF_5'(A_14949,k1_xboole_0),A_14949)
      | k3_xboole_0(A_15,k1_xboole_0) = A_14949 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_24142])).

tff(c_24234,plain,(
    ! [A_14949] :
      ( r2_hidden('#skF_4'(A_14949,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_5'(A_14949,k1_xboole_0),A_14949)
      | k1_xboole_0 = A_14949 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_24214])).

tff(c_24235,plain,(
    ! [A_14949] :
      ( r2_hidden('#skF_5'(A_14949,k1_xboole_0),A_14949)
      | k1_xboole_0 = A_14949 ) ),
    inference(negUnitSimplification,[status(thm)],[c_20716,c_24234])).

tff(c_243,plain,(
    ! [A_85,B_86] :
      ( '#skF_1'(k1_tarski(A_85),B_86) = A_85
      | r1_tarski(k1_tarski(A_85),B_86) ) ),
    inference(resolution,[status(thm)],[c_154,c_38])).

tff(c_681,plain,(
    ! [A_1276,A_1277] :
      ( k1_relat_1('#skF_9'(A_1276,A_1277)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_1276,A_1277))
      | ~ v1_relat_1('#skF_9'(A_1276,A_1277))
      | k1_xboole_0 = A_1276
      | '#skF_1'(k1_tarski(A_1277),'#skF_10') = A_1277 ) ),
    inference(resolution,[status(thm)],[c_243,c_135])).

tff(c_21751,plain,(
    ! [A_13832,B_13833] :
      ( k1_relat_1('#skF_9'(A_13832,B_13833)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_13832,B_13833))
      | '#skF_1'(k1_tarski(B_13833),'#skF_10') = B_13833
      | k1_xboole_0 = A_13832 ) ),
    inference(resolution,[status(thm)],[c_70,c_681])).

tff(c_23921,plain,(
    ! [A_14858,B_14859] :
      ( k1_relat_1('#skF_9'(A_14858,B_14859)) != '#skF_11'
      | '#skF_1'(k1_tarski(B_14859),'#skF_10') = B_14859
      | k1_xboole_0 = A_14858 ) ),
    inference(resolution,[status(thm)],[c_68,c_21751])).

tff(c_23945,plain,(
    ! [A_31,B_35] :
      ( A_31 != '#skF_11'
      | '#skF_1'(k1_tarski(B_35),'#skF_10') = B_35
      | k1_xboole_0 = A_31
      | k1_xboole_0 = A_31 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_23921])).

tff(c_23947,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_23945])).

tff(c_36,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_171,plain,(
    ! [A_70] :
      ( k2_relat_1(A_70) = k1_xboole_0
      | k1_relat_1(A_70) != k1_xboole_0
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_177,plain,(
    ! [A_25] :
      ( k2_relat_1('#skF_8'(A_25)) = k1_xboole_0
      | k1_relat_1('#skF_8'(A_25)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_62,c_171])).

tff(c_182,plain,(
    ! [A_71] :
      ( k2_relat_1('#skF_8'(A_71)) = k1_xboole_0
      | k1_xboole_0 != A_71 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_177])).

tff(c_191,plain,(
    ! [A_71] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_10')
      | k1_relat_1('#skF_8'(A_71)) != '#skF_11'
      | ~ v1_funct_1('#skF_8'(A_71))
      | ~ v1_relat_1('#skF_8'(A_71))
      | k1_xboole_0 != A_71 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_72])).

tff(c_198,plain,(
    ! [A_71] :
      ( A_71 != '#skF_11'
      | k1_xboole_0 != A_71 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_36,c_191])).

tff(c_203,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_198])).

tff(c_23996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23947,c_203])).

tff(c_24000,plain,(
    ! [B_14889] : '#skF_1'(k1_tarski(B_14889),'#skF_10') = B_14889 ),
    inference(splitRight,[status(thm)],[c_23945])).

tff(c_24078,plain,(
    ! [B_14919] :
      ( ~ r2_hidden(B_14919,'#skF_10')
      | r1_tarski(k1_tarski(B_14919),'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24000,c_4])).

tff(c_24361,plain,(
    ! [A_15073,B_15074] :
      ( k1_relat_1('#skF_9'(A_15073,B_15074)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_15073,B_15074))
      | ~ v1_relat_1('#skF_9'(A_15073,B_15074))
      | k1_xboole_0 = A_15073
      | ~ r2_hidden(B_15074,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_24078,c_135])).

tff(c_24677,plain,(
    ! [A_15229,B_15230] :
      ( k1_relat_1('#skF_9'(A_15229,B_15230)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_15229,B_15230))
      | ~ r2_hidden(B_15230,'#skF_10')
      | k1_xboole_0 = A_15229 ) ),
    inference(resolution,[status(thm)],[c_70,c_24361])).

tff(c_24683,plain,(
    ! [A_15260,B_15261] :
      ( k1_relat_1('#skF_9'(A_15260,B_15261)) != '#skF_11'
      | ~ r2_hidden(B_15261,'#skF_10')
      | k1_xboole_0 = A_15260 ) ),
    inference(resolution,[status(thm)],[c_68,c_24677])).

tff(c_24688,plain,(
    ! [A_31,B_35] :
      ( A_31 != '#skF_11'
      | ~ r2_hidden(B_35,'#skF_10')
      | k1_xboole_0 = A_31
      | k1_xboole_0 = A_31 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_24683])).

tff(c_24691,plain,(
    ! [B_15291] : ~ r2_hidden(B_15291,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_24688])).

tff(c_24711,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_24235,c_24691])).

tff(c_24865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_24711])).

tff(c_24867,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_24688])).

tff(c_24921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24867,c_203])).

tff(c_24923,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_20715])).

tff(c_24951,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24923,c_203])).

tff(c_24953,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_24952,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_24960,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24953,c_24952])).

tff(c_24955,plain,(
    ! [A_16] : r1_tarski('#skF_11',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24952,c_36])).

tff(c_24969,plain,(
    ! [A_16] : r1_tarski('#skF_10',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24960,c_24955])).

tff(c_54,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) = k1_xboole_0
      | k1_relat_1(A_24) != k1_xboole_0
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_25042,plain,(
    ! [A_15345] :
      ( k2_relat_1(A_15345) = '#skF_10'
      | k1_relat_1(A_15345) != '#skF_10'
      | ~ v1_relat_1(A_15345) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24953,c_24953,c_54])).

tff(c_25048,plain,(
    ! [A_25] :
      ( k2_relat_1('#skF_8'(A_25)) = '#skF_10'
      | k1_relat_1('#skF_8'(A_25)) != '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_62,c_25042])).

tff(c_25053,plain,(
    ! [A_15346] :
      ( k2_relat_1('#skF_8'(A_15346)) = '#skF_10'
      | A_15346 != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_25048])).

tff(c_24971,plain,(
    ! [C_38] :
      ( ~ r1_tarski(k2_relat_1(C_38),'#skF_10')
      | k1_relat_1(C_38) != '#skF_10'
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24960,c_72])).

tff(c_25059,plain,(
    ! [A_15346] :
      ( ~ r1_tarski('#skF_10','#skF_10')
      | k1_relat_1('#skF_8'(A_15346)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_15346))
      | ~ v1_relat_1('#skF_8'(A_15346))
      | A_15346 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25053,c_24971])).

tff(c_25065,plain,(
    ! [A_15346] : A_15346 != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_24969,c_25059])).

tff(c_24954,plain,(
    ! [A_15] : k3_xboole_0(A_15,'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24952,c_24952,c_34])).

tff(c_24973,plain,(
    ! [A_15] : k3_xboole_0(A_15,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24960,c_24960,c_24954])).

tff(c_25078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25065,c_24973])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n011.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 09:30:57 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.01/3.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.01/3.04  
% 9.01/3.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.01/3.05  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_8 > #skF_10 > #skF_2 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4
% 9.01/3.05  
% 9.01/3.05  %Foreground sorts:
% 9.01/3.05  
% 9.01/3.05  
% 9.01/3.05  %Background operators:
% 9.01/3.05  
% 9.01/3.05  
% 9.01/3.05  %Foreground operators:
% 9.01/3.05  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 9.01/3.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.01/3.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.01/3.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.01/3.05  tff('#skF_11', type, '#skF_11': $i).
% 9.01/3.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.01/3.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.01/3.05  tff('#skF_8', type, '#skF_8': $i > $i).
% 9.01/3.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.01/3.05  tff('#skF_10', type, '#skF_10': $i).
% 9.01/3.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.01/3.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.01/3.05  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.01/3.05  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.01/3.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.01/3.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.01/3.05  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.01/3.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.01/3.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.01/3.05  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 9.01/3.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.01/3.05  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 9.01/3.05  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.01/3.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.01/3.05  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.01/3.05  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.01/3.05  
% 9.40/3.07  tff(f_79, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 9.40/3.07  tff(f_110, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 9.40/3.07  tff(f_92, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 9.40/3.07  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.40/3.07  tff(f_59, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 9.40/3.07  tff(f_50, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 9.40/3.07  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 9.40/3.07  tff(f_48, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 9.40/3.07  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.40/3.07  tff(f_67, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 9.40/3.07  tff(c_62, plain, (![A_25]: (v1_relat_1('#skF_8'(A_25)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.40/3.07  tff(c_60, plain, (![A_25]: (v1_funct_1('#skF_8'(A_25)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.40/3.07  tff(c_58, plain, (![A_25]: (k1_relat_1('#skF_8'(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.40/3.07  tff(c_74, plain, (k1_xboole_0='#skF_11' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.40/3.07  tff(c_95, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_74])).
% 9.40/3.07  tff(c_66, plain, (![A_31, B_35]: (k1_relat_1('#skF_9'(A_31, B_35))=A_31 | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.40/3.07  tff(c_68, plain, (![A_31, B_35]: (v1_funct_1('#skF_9'(A_31, B_35)) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.40/3.07  tff(c_70, plain, (![A_31, B_35]: (v1_relat_1('#skF_9'(A_31, B_35)) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.40/3.07  tff(c_154, plain, (![A_67, B_68]: (r2_hidden('#skF_1'(A_67, B_68), A_67) | r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.40/3.07  tff(c_38, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.40/3.07  tff(c_169, plain, (![A_17, B_68]: ('#skF_1'(k1_tarski(A_17), B_68)=A_17 | r1_tarski(k1_tarski(A_17), B_68))), inference(resolution, [status(thm)], [c_154, c_38])).
% 9.40/3.07  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.40/3.07  tff(c_229, plain, (![C_80, B_81, A_82]: (r2_hidden(C_80, B_81) | ~r2_hidden(C_80, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.40/3.07  tff(c_623, plain, (![A_1184, B_1185, B_1186]: (r2_hidden('#skF_1'(A_1184, B_1185), B_1186) | ~r1_tarski(A_1184, B_1186) | r1_tarski(A_1184, B_1185))), inference(resolution, [status(thm)], [c_6, c_229])).
% 9.40/3.07  tff(c_34, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.40/3.07  tff(c_214, plain, (![D_75, A_76, B_77]: (r2_hidden(D_75, A_76) | ~r2_hidden(D_75, k3_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.40/3.07  tff(c_221, plain, (![D_75, A_15]: (r2_hidden(D_75, A_15) | ~r2_hidden(D_75, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_214])).
% 9.40/3.07  tff(c_741, plain, (![A_1369, B_1370, A_1371]: (r2_hidden('#skF_1'(A_1369, B_1370), A_1371) | ~r1_tarski(A_1369, k1_xboole_0) | r1_tarski(A_1369, B_1370))), inference(resolution, [status(thm)], [c_623, c_221])).
% 9.40/3.07  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.40/3.07  tff(c_773, plain, (![A_1401, A_1402]: (~r1_tarski(A_1401, k1_xboole_0) | r1_tarski(A_1401, A_1402))), inference(resolution, [status(thm)], [c_741, c_4])).
% 9.40/3.07  tff(c_788, plain, (![A_1432, A_1433]: (r1_tarski(k1_tarski(A_1432), A_1433) | '#skF_1'(k1_tarski(A_1432), k1_xboole_0)=A_1432)), inference(resolution, [status(thm)], [c_169, c_773])).
% 9.40/3.07  tff(c_40, plain, (![C_21]: (r2_hidden(C_21, k1_tarski(C_21)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.40/3.07  tff(c_235, plain, (![C_21, B_81]: (r2_hidden(C_21, B_81) | ~r1_tarski(k1_tarski(C_21), B_81))), inference(resolution, [status(thm)], [c_40, c_229])).
% 9.40/3.07  tff(c_897, plain, (![A_1494, A_1495]: (r2_hidden(A_1494, A_1495) | '#skF_1'(k1_tarski(A_1494), k1_xboole_0)=A_1494)), inference(resolution, [status(thm)], [c_788, c_235])).
% 9.40/3.07  tff(c_996, plain, (![A_17, A_1494]: (A_17=A_1494 | '#skF_1'(k1_tarski(A_1494), k1_xboole_0)=A_1494)), inference(resolution, [status(thm)], [c_897, c_38])).
% 9.40/3.07  tff(c_8280, plain, (![A_4282]: ('#skF_1'(k1_tarski(A_4282), k1_xboole_0)=A_4282)), inference(factorization, [status(thm), theory('equality')], [c_996])).
% 9.40/3.07  tff(c_8462, plain, (![A_4374]: (~r2_hidden(A_4374, k1_xboole_0) | r1_tarski(k1_tarski(A_4374), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8280, c_4])).
% 9.40/3.07  tff(c_770, plain, (![A_1369, A_1371]: (~r1_tarski(A_1369, k1_xboole_0) | r1_tarski(A_1369, A_1371))), inference(resolution, [status(thm)], [c_741, c_4])).
% 9.40/3.07  tff(c_8519, plain, (![A_4404, A_4405]: (r1_tarski(k1_tarski(A_4404), A_4405) | ~r2_hidden(A_4404, k1_xboole_0))), inference(resolution, [status(thm)], [c_8462, c_770])).
% 9.40/3.07  tff(c_129, plain, (![A_59, B_60]: (k2_relat_1('#skF_9'(A_59, B_60))=k1_tarski(B_60) | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.40/3.07  tff(c_72, plain, (![C_38]: (~r1_tarski(k2_relat_1(C_38), '#skF_10') | k1_relat_1(C_38)!='#skF_11' | ~v1_funct_1(C_38) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.40/3.07  tff(c_135, plain, (![B_60, A_59]: (~r1_tarski(k1_tarski(B_60), '#skF_10') | k1_relat_1('#skF_9'(A_59, B_60))!='#skF_11' | ~v1_funct_1('#skF_9'(A_59, B_60)) | ~v1_relat_1('#skF_9'(A_59, B_60)) | k1_xboole_0=A_59)), inference(superposition, [status(thm), theory('equality')], [c_129, c_72])).
% 9.40/3.07  tff(c_8637, plain, (![A_4466, A_4467]: (k1_relat_1('#skF_9'(A_4466, A_4467))!='#skF_11' | ~v1_funct_1('#skF_9'(A_4466, A_4467)) | ~v1_relat_1('#skF_9'(A_4466, A_4467)) | k1_xboole_0=A_4466 | ~r2_hidden(A_4467, k1_xboole_0))), inference(resolution, [status(thm)], [c_8519, c_135])).
% 9.40/3.07  tff(c_20704, plain, (![A_13248, B_13249]: (k1_relat_1('#skF_9'(A_13248, B_13249))!='#skF_11' | ~v1_funct_1('#skF_9'(A_13248, B_13249)) | ~r2_hidden(B_13249, k1_xboole_0) | k1_xboole_0=A_13248)), inference(resolution, [status(thm)], [c_70, c_8637])).
% 9.40/3.07  tff(c_20710, plain, (![A_13279, B_13280]: (k1_relat_1('#skF_9'(A_13279, B_13280))!='#skF_11' | ~r2_hidden(B_13280, k1_xboole_0) | k1_xboole_0=A_13279)), inference(resolution, [status(thm)], [c_68, c_20704])).
% 9.40/3.07  tff(c_20715, plain, (![A_31, B_35]: (A_31!='#skF_11' | ~r2_hidden(B_35, k1_xboole_0) | k1_xboole_0=A_31 | k1_xboole_0=A_31)), inference(superposition, [status(thm), theory('equality')], [c_66, c_20710])).
% 9.40/3.07  tff(c_20716, plain, (![B_35]: (~r2_hidden(B_35, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_20715])).
% 9.40/3.07  tff(c_8363, plain, (![A_4312, B_4313]: (r2_hidden('#skF_4'(A_4312, B_4313), B_4313) | r2_hidden('#skF_5'(A_4312, B_4313), A_4312) | B_4313=A_4312)), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.40/3.07  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.40/3.07  tff(c_24142, plain, (![A_14949, A_14950, B_14951]: (r2_hidden('#skF_4'(A_14949, k3_xboole_0(A_14950, B_14951)), B_14951) | r2_hidden('#skF_5'(A_14949, k3_xboole_0(A_14950, B_14951)), A_14949) | k3_xboole_0(A_14950, B_14951)=A_14949)), inference(resolution, [status(thm)], [c_8363, c_10])).
% 9.40/3.07  tff(c_24214, plain, (![A_14949, A_15]: (r2_hidden('#skF_4'(A_14949, k3_xboole_0(A_15, k1_xboole_0)), k1_xboole_0) | r2_hidden('#skF_5'(A_14949, k1_xboole_0), A_14949) | k3_xboole_0(A_15, k1_xboole_0)=A_14949)), inference(superposition, [status(thm), theory('equality')], [c_34, c_24142])).
% 9.40/3.07  tff(c_24234, plain, (![A_14949]: (r2_hidden('#skF_4'(A_14949, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_5'(A_14949, k1_xboole_0), A_14949) | k1_xboole_0=A_14949)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_24214])).
% 9.40/3.07  tff(c_24235, plain, (![A_14949]: (r2_hidden('#skF_5'(A_14949, k1_xboole_0), A_14949) | k1_xboole_0=A_14949)), inference(negUnitSimplification, [status(thm)], [c_20716, c_24234])).
% 9.40/3.07  tff(c_243, plain, (![A_85, B_86]: ('#skF_1'(k1_tarski(A_85), B_86)=A_85 | r1_tarski(k1_tarski(A_85), B_86))), inference(resolution, [status(thm)], [c_154, c_38])).
% 9.40/3.07  tff(c_681, plain, (![A_1276, A_1277]: (k1_relat_1('#skF_9'(A_1276, A_1277))!='#skF_11' | ~v1_funct_1('#skF_9'(A_1276, A_1277)) | ~v1_relat_1('#skF_9'(A_1276, A_1277)) | k1_xboole_0=A_1276 | '#skF_1'(k1_tarski(A_1277), '#skF_10')=A_1277)), inference(resolution, [status(thm)], [c_243, c_135])).
% 9.40/3.07  tff(c_21751, plain, (![A_13832, B_13833]: (k1_relat_1('#skF_9'(A_13832, B_13833))!='#skF_11' | ~v1_funct_1('#skF_9'(A_13832, B_13833)) | '#skF_1'(k1_tarski(B_13833), '#skF_10')=B_13833 | k1_xboole_0=A_13832)), inference(resolution, [status(thm)], [c_70, c_681])).
% 9.40/3.07  tff(c_23921, plain, (![A_14858, B_14859]: (k1_relat_1('#skF_9'(A_14858, B_14859))!='#skF_11' | '#skF_1'(k1_tarski(B_14859), '#skF_10')=B_14859 | k1_xboole_0=A_14858)), inference(resolution, [status(thm)], [c_68, c_21751])).
% 9.40/3.07  tff(c_23945, plain, (![A_31, B_35]: (A_31!='#skF_11' | '#skF_1'(k1_tarski(B_35), '#skF_10')=B_35 | k1_xboole_0=A_31 | k1_xboole_0=A_31)), inference(superposition, [status(thm), theory('equality')], [c_66, c_23921])).
% 9.40/3.07  tff(c_23947, plain, (k1_xboole_0='#skF_11'), inference(splitLeft, [status(thm)], [c_23945])).
% 9.40/3.07  tff(c_36, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.40/3.07  tff(c_171, plain, (![A_70]: (k2_relat_1(A_70)=k1_xboole_0 | k1_relat_1(A_70)!=k1_xboole_0 | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.40/3.07  tff(c_177, plain, (![A_25]: (k2_relat_1('#skF_8'(A_25))=k1_xboole_0 | k1_relat_1('#skF_8'(A_25))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_62, c_171])).
% 9.40/3.07  tff(c_182, plain, (![A_71]: (k2_relat_1('#skF_8'(A_71))=k1_xboole_0 | k1_xboole_0!=A_71)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_177])).
% 9.40/3.07  tff(c_191, plain, (![A_71]: (~r1_tarski(k1_xboole_0, '#skF_10') | k1_relat_1('#skF_8'(A_71))!='#skF_11' | ~v1_funct_1('#skF_8'(A_71)) | ~v1_relat_1('#skF_8'(A_71)) | k1_xboole_0!=A_71)), inference(superposition, [status(thm), theory('equality')], [c_182, c_72])).
% 9.40/3.07  tff(c_198, plain, (![A_71]: (A_71!='#skF_11' | k1_xboole_0!=A_71)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_36, c_191])).
% 9.40/3.07  tff(c_203, plain, (k1_xboole_0!='#skF_11'), inference(reflexivity, [status(thm), theory('equality')], [c_198])).
% 9.40/3.07  tff(c_23996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23947, c_203])).
% 9.40/3.07  tff(c_24000, plain, (![B_14889]: ('#skF_1'(k1_tarski(B_14889), '#skF_10')=B_14889)), inference(splitRight, [status(thm)], [c_23945])).
% 9.40/3.07  tff(c_24078, plain, (![B_14919]: (~r2_hidden(B_14919, '#skF_10') | r1_tarski(k1_tarski(B_14919), '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_24000, c_4])).
% 9.40/3.07  tff(c_24361, plain, (![A_15073, B_15074]: (k1_relat_1('#skF_9'(A_15073, B_15074))!='#skF_11' | ~v1_funct_1('#skF_9'(A_15073, B_15074)) | ~v1_relat_1('#skF_9'(A_15073, B_15074)) | k1_xboole_0=A_15073 | ~r2_hidden(B_15074, '#skF_10'))), inference(resolution, [status(thm)], [c_24078, c_135])).
% 9.40/3.07  tff(c_24677, plain, (![A_15229, B_15230]: (k1_relat_1('#skF_9'(A_15229, B_15230))!='#skF_11' | ~v1_funct_1('#skF_9'(A_15229, B_15230)) | ~r2_hidden(B_15230, '#skF_10') | k1_xboole_0=A_15229)), inference(resolution, [status(thm)], [c_70, c_24361])).
% 9.40/3.07  tff(c_24683, plain, (![A_15260, B_15261]: (k1_relat_1('#skF_9'(A_15260, B_15261))!='#skF_11' | ~r2_hidden(B_15261, '#skF_10') | k1_xboole_0=A_15260)), inference(resolution, [status(thm)], [c_68, c_24677])).
% 9.40/3.07  tff(c_24688, plain, (![A_31, B_35]: (A_31!='#skF_11' | ~r2_hidden(B_35, '#skF_10') | k1_xboole_0=A_31 | k1_xboole_0=A_31)), inference(superposition, [status(thm), theory('equality')], [c_66, c_24683])).
% 9.40/3.07  tff(c_24691, plain, (![B_15291]: (~r2_hidden(B_15291, '#skF_10'))), inference(splitLeft, [status(thm)], [c_24688])).
% 9.40/3.07  tff(c_24711, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_24235, c_24691])).
% 9.40/3.07  tff(c_24865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_24711])).
% 9.40/3.07  tff(c_24867, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_24688])).
% 9.40/3.07  tff(c_24921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24867, c_203])).
% 9.40/3.07  tff(c_24923, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_20715])).
% 9.40/3.07  tff(c_24951, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24923, c_203])).
% 9.40/3.07  tff(c_24953, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_74])).
% 9.40/3.07  tff(c_24952, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_74])).
% 9.40/3.07  tff(c_24960, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_24953, c_24952])).
% 9.40/3.07  tff(c_24955, plain, (![A_16]: (r1_tarski('#skF_11', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_24952, c_36])).
% 9.40/3.07  tff(c_24969, plain, (![A_16]: (r1_tarski('#skF_10', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_24960, c_24955])).
% 9.40/3.07  tff(c_54, plain, (![A_24]: (k2_relat_1(A_24)=k1_xboole_0 | k1_relat_1(A_24)!=k1_xboole_0 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.40/3.07  tff(c_25042, plain, (![A_15345]: (k2_relat_1(A_15345)='#skF_10' | k1_relat_1(A_15345)!='#skF_10' | ~v1_relat_1(A_15345))), inference(demodulation, [status(thm), theory('equality')], [c_24953, c_24953, c_54])).
% 9.40/3.07  tff(c_25048, plain, (![A_25]: (k2_relat_1('#skF_8'(A_25))='#skF_10' | k1_relat_1('#skF_8'(A_25))!='#skF_10')), inference(resolution, [status(thm)], [c_62, c_25042])).
% 9.40/3.07  tff(c_25053, plain, (![A_15346]: (k2_relat_1('#skF_8'(A_15346))='#skF_10' | A_15346!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_25048])).
% 9.40/3.07  tff(c_24971, plain, (![C_38]: (~r1_tarski(k2_relat_1(C_38), '#skF_10') | k1_relat_1(C_38)!='#skF_10' | ~v1_funct_1(C_38) | ~v1_relat_1(C_38))), inference(demodulation, [status(thm), theory('equality')], [c_24960, c_72])).
% 9.40/3.07  tff(c_25059, plain, (![A_15346]: (~r1_tarski('#skF_10', '#skF_10') | k1_relat_1('#skF_8'(A_15346))!='#skF_10' | ~v1_funct_1('#skF_8'(A_15346)) | ~v1_relat_1('#skF_8'(A_15346)) | A_15346!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_25053, c_24971])).
% 9.40/3.07  tff(c_25065, plain, (![A_15346]: (A_15346!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_24969, c_25059])).
% 9.40/3.07  tff(c_24954, plain, (![A_15]: (k3_xboole_0(A_15, '#skF_11')='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_24952, c_24952, c_34])).
% 9.40/3.07  tff(c_24973, plain, (![A_15]: (k3_xboole_0(A_15, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_24960, c_24960, c_24954])).
% 9.40/3.07  tff(c_25078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25065, c_24973])).
% 9.40/3.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.40/3.07  
% 9.40/3.07  Inference rules
% 9.40/3.07  ----------------------
% 9.40/3.07  #Ref     : 3
% 9.40/3.07  #Sup     : 4140
% 9.40/3.07  #Fact    : 9
% 9.40/3.07  #Define  : 0
% 9.40/3.07  #Split   : 8
% 9.40/3.07  #Chain   : 0
% 9.40/3.07  #Close   : 0
% 9.40/3.07  
% 9.40/3.07  Ordering : KBO
% 9.40/3.07  
% 9.40/3.07  Simplification rules
% 9.40/3.07  ----------------------
% 9.40/3.07  #Subsume      : 1217
% 9.40/3.07  #Demod        : 1215
% 9.40/3.07  #Tautology    : 561
% 9.40/3.07  #SimpNegUnit  : 108
% 9.40/3.07  #BackRed      : 142
% 9.40/3.07  
% 9.40/3.07  #Partial instantiations: 9785
% 9.40/3.07  #Strategies tried      : 1
% 9.40/3.07  
% 9.40/3.07  Timing (in seconds)
% 9.40/3.07  ----------------------
% 9.40/3.07  Preprocessing        : 0.31
% 9.40/3.07  Parsing              : 0.15
% 9.40/3.07  CNF conversion       : 0.03
% 9.40/3.07  Main loop            : 1.97
% 9.40/3.07  Inferencing          : 0.74
% 9.40/3.07  Reduction            : 0.48
% 9.40/3.07  Demodulation         : 0.32
% 9.40/3.07  BG Simplification    : 0.10
% 9.40/3.07  Subsumption          : 0.43
% 9.40/3.07  Abstraction          : 0.12
% 9.40/3.07  MUC search           : 0.00
% 9.40/3.07  Cooper               : 0.00
% 9.40/3.07  Total                : 2.32
% 9.40/3.07  Index Insertion      : 0.00
% 9.40/3.07  Index Deletion       : 0.00
% 9.40/3.07  Index Matching       : 0.00
% 9.40/3.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
