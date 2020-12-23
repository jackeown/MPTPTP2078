%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:22 EST 2020

% Result     : Theorem 9.13s
% Output     : CNFRefutation 9.13s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 147 expanded)
%              Number of leaves         :   40 (  65 expanded)
%              Depth                    :   18
%              Number of atoms          :  113 ( 234 expanded)
%              Number of equality atoms :   29 (  56 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_87,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_69,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_84,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_58,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,(
    ! [A_33] : ~ v1_xboole_0(k1_zfmisc_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_231,plain,(
    ! [B_69,A_70] :
      ( r2_hidden(B_69,A_70)
      | ~ m1_subset_1(B_69,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [A_29] : k3_tarski(k1_zfmisc_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_122,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,k3_tarski(B_53))
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_125,plain,(
    ! [A_52,A_29] :
      ( r1_tarski(A_52,A_29)
      | ~ r2_hidden(A_52,k1_zfmisc_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_122])).

tff(c_235,plain,(
    ! [B_69,A_29] :
      ( r1_tarski(B_69,A_29)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_29))
      | v1_xboole_0(k1_zfmisc_1(A_29)) ) ),
    inference(resolution,[status(thm)],[c_231,c_125])).

tff(c_243,plain,(
    ! [B_71,A_72] :
      ( r1_tarski(B_71,A_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_235])).

tff(c_252,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_243])).

tff(c_907,plain,(
    ! [A_110,C_111,B_112] :
      ( r1_tarski(A_110,C_111)
      | ~ r1_tarski(B_112,C_111)
      | ~ r1_tarski(A_110,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_957,plain,(
    ! [A_114] :
      ( r1_tarski(A_114,'#skF_2')
      | ~ r1_tarski(A_114,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_252,c_907])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1192,plain,(
    ! [A_151] :
      ( k3_xboole_0(A_151,'#skF_2') = A_151
      | ~ r1_tarski(A_151,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_957,c_10])).

tff(c_1215,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_58,c_1192])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1219,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1215,c_6])).

tff(c_1222,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1219])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1227,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1222,c_16])).

tff(c_1230,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1227])).

tff(c_24,plain,(
    ! [A_23,B_24] : k3_tarski(k2_tarski(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    ! [A_25] : r1_tarski(A_25,k1_zfmisc_1(k3_tarski(A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_282,plain,(
    ! [B_76,C_77,A_78] :
      ( r2_hidden(B_76,C_77)
      | ~ r1_tarski(k2_tarski(A_78,B_76),C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_290,plain,(
    ! [B_76,A_78] : r2_hidden(B_76,k1_zfmisc_1(k3_tarski(k2_tarski(A_78,B_76)))) ),
    inference(resolution,[status(thm)],[c_26,c_282])).

tff(c_294,plain,(
    ! [B_79,A_80] : r2_hidden(B_79,k1_zfmisc_1(k2_xboole_0(A_80,B_79))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_290])).

tff(c_36,plain,(
    ! [B_31,A_30] :
      ( m1_subset_1(B_31,A_30)
      | ~ r2_hidden(B_31,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_297,plain,(
    ! [B_79,A_80] :
      ( m1_subset_1(B_79,k1_zfmisc_1(k2_xboole_0(A_80,B_79)))
      | v1_xboole_0(k1_zfmisc_1(k2_xboole_0(A_80,B_79))) ) ),
    inference(resolution,[status(thm)],[c_294,c_36])).

tff(c_306,plain,(
    ! [B_79,A_80] : m1_subset_1(B_79,k1_zfmisc_1(k2_xboole_0(A_80,B_79))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_297])).

tff(c_1247,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1230,c_306])).

tff(c_56,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1281,plain,(
    ! [C_152,A_153,B_154] :
      ( r1_tarski(C_152,k3_subset_1(A_153,B_154))
      | ~ r1_tarski(B_154,k3_subset_1(A_153,C_152))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(A_153))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(A_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1295,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_1281])).

tff(c_1307,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1295])).

tff(c_1351,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1247,c_1307])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(B_8,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14835,plain,(
    ! [A_583] :
      ( r1_tarski(A_583,k3_subset_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_583,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1351,c_8])).

tff(c_44,plain,(
    ! [A_32] : k1_subset_1(A_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_52,plain,(
    ! [A_38,B_39] :
      ( k1_subset_1(A_38) = B_39
      | ~ r1_tarski(B_39,k3_subset_1(A_38,B_39))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_61,plain,(
    ! [B_39,A_38] :
      ( k1_xboole_0 = B_39
      | ~ r1_tarski(B_39,k3_subset_1(A_38,B_39))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_52])).

tff(c_14862,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2'))
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_14835,c_61])).

tff(c_14889,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1247,c_14862])).

tff(c_14891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_14889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:15:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.13/4.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.13/4.07  
% 9.13/4.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.13/4.08  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 9.13/4.08  
% 9.13/4.08  %Foreground sorts:
% 9.13/4.08  
% 9.13/4.08  
% 9.13/4.08  %Background operators:
% 9.13/4.08  
% 9.13/4.08  
% 9.13/4.08  %Foreground operators:
% 9.13/4.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.13/4.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.13/4.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.13/4.08  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.13/4.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.13/4.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.13/4.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.13/4.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.13/4.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.13/4.08  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.13/4.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.13/4.08  tff('#skF_2', type, '#skF_2': $i).
% 9.13/4.08  tff('#skF_3', type, '#skF_3': $i).
% 9.13/4.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.13/4.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.13/4.08  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.13/4.08  tff('#skF_4', type, '#skF_4': $i).
% 9.13/4.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.13/4.08  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 9.13/4.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.13/4.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.13/4.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.13/4.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.13/4.08  
% 9.13/4.09  tff(f_111, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 9.13/4.09  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 9.13/4.09  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.13/4.09  tff(f_87, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 9.13/4.09  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 9.13/4.09  tff(f_69, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 9.13/4.09  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 9.13/4.09  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.13/4.09  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.13/4.09  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.13/4.09  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.13/4.09  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.13/4.09  tff(f_61, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 9.13/4.09  tff(f_67, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 9.13/4.09  tff(f_96, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 9.13/4.09  tff(f_84, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 9.13/4.09  tff(f_102, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 9.13/4.09  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.13/4.09  tff(c_58, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.13/4.09  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.13/4.09  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.13/4.09  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.13/4.09  tff(c_46, plain, (![A_33]: (~v1_xboole_0(k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.13/4.09  tff(c_231, plain, (![B_69, A_70]: (r2_hidden(B_69, A_70) | ~m1_subset_1(B_69, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.13/4.09  tff(c_34, plain, (![A_29]: (k3_tarski(k1_zfmisc_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.13/4.09  tff(c_122, plain, (![A_52, B_53]: (r1_tarski(A_52, k3_tarski(B_53)) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.13/4.09  tff(c_125, plain, (![A_52, A_29]: (r1_tarski(A_52, A_29) | ~r2_hidden(A_52, k1_zfmisc_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_122])).
% 9.13/4.09  tff(c_235, plain, (![B_69, A_29]: (r1_tarski(B_69, A_29) | ~m1_subset_1(B_69, k1_zfmisc_1(A_29)) | v1_xboole_0(k1_zfmisc_1(A_29)))), inference(resolution, [status(thm)], [c_231, c_125])).
% 9.13/4.09  tff(c_243, plain, (![B_71, A_72]: (r1_tarski(B_71, A_72) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)))), inference(negUnitSimplification, [status(thm)], [c_46, c_235])).
% 9.13/4.09  tff(c_252, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_243])).
% 9.13/4.09  tff(c_907, plain, (![A_110, C_111, B_112]: (r1_tarski(A_110, C_111) | ~r1_tarski(B_112, C_111) | ~r1_tarski(A_110, B_112))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.13/4.09  tff(c_957, plain, (![A_114]: (r1_tarski(A_114, '#skF_2') | ~r1_tarski(A_114, '#skF_4'))), inference(resolution, [status(thm)], [c_252, c_907])).
% 9.13/4.09  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.13/4.09  tff(c_1192, plain, (![A_151]: (k3_xboole_0(A_151, '#skF_2')=A_151 | ~r1_tarski(A_151, '#skF_4'))), inference(resolution, [status(thm)], [c_957, c_10])).
% 9.13/4.09  tff(c_1215, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_58, c_1192])).
% 9.13/4.09  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.13/4.09  tff(c_1219, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1215, c_6])).
% 9.13/4.09  tff(c_1222, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1219])).
% 9.13/4.09  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.13/4.09  tff(c_1227, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1222, c_16])).
% 9.13/4.09  tff(c_1230, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1227])).
% 9.13/4.09  tff(c_24, plain, (![A_23, B_24]: (k3_tarski(k2_tarski(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.13/4.09  tff(c_26, plain, (![A_25]: (r1_tarski(A_25, k1_zfmisc_1(k3_tarski(A_25))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.13/4.09  tff(c_282, plain, (![B_76, C_77, A_78]: (r2_hidden(B_76, C_77) | ~r1_tarski(k2_tarski(A_78, B_76), C_77))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.13/4.09  tff(c_290, plain, (![B_76, A_78]: (r2_hidden(B_76, k1_zfmisc_1(k3_tarski(k2_tarski(A_78, B_76)))))), inference(resolution, [status(thm)], [c_26, c_282])).
% 9.13/4.09  tff(c_294, plain, (![B_79, A_80]: (r2_hidden(B_79, k1_zfmisc_1(k2_xboole_0(A_80, B_79))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_290])).
% 9.13/4.09  tff(c_36, plain, (![B_31, A_30]: (m1_subset_1(B_31, A_30) | ~r2_hidden(B_31, A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.13/4.09  tff(c_297, plain, (![B_79, A_80]: (m1_subset_1(B_79, k1_zfmisc_1(k2_xboole_0(A_80, B_79))) | v1_xboole_0(k1_zfmisc_1(k2_xboole_0(A_80, B_79))))), inference(resolution, [status(thm)], [c_294, c_36])).
% 9.13/4.09  tff(c_306, plain, (![B_79, A_80]: (m1_subset_1(B_79, k1_zfmisc_1(k2_xboole_0(A_80, B_79))))), inference(negUnitSimplification, [status(thm)], [c_46, c_297])).
% 9.13/4.09  tff(c_1247, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1230, c_306])).
% 9.13/4.09  tff(c_56, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.13/4.09  tff(c_1281, plain, (![C_152, A_153, B_154]: (r1_tarski(C_152, k3_subset_1(A_153, B_154)) | ~r1_tarski(B_154, k3_subset_1(A_153, C_152)) | ~m1_subset_1(C_152, k1_zfmisc_1(A_153)) | ~m1_subset_1(B_154, k1_zfmisc_1(A_153)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.13/4.09  tff(c_1295, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_1281])).
% 9.13/4.09  tff(c_1307, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1295])).
% 9.13/4.09  tff(c_1351, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1247, c_1307])).
% 9.13/4.09  tff(c_8, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(B_8, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.13/4.09  tff(c_14835, plain, (![A_583]: (r1_tarski(A_583, k3_subset_1('#skF_2', '#skF_3')) | ~r1_tarski(A_583, '#skF_4'))), inference(resolution, [status(thm)], [c_1351, c_8])).
% 9.13/4.09  tff(c_44, plain, (![A_32]: (k1_subset_1(A_32)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.13/4.09  tff(c_52, plain, (![A_38, B_39]: (k1_subset_1(A_38)=B_39 | ~r1_tarski(B_39, k3_subset_1(A_38, B_39)) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.13/4.09  tff(c_61, plain, (![B_39, A_38]: (k1_xboole_0=B_39 | ~r1_tarski(B_39, k3_subset_1(A_38, B_39)) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_52])).
% 9.13/4.09  tff(c_14862, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')) | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_14835, c_61])).
% 9.13/4.09  tff(c_14889, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1247, c_14862])).
% 9.13/4.09  tff(c_14891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_14889])).
% 9.13/4.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.13/4.09  
% 9.13/4.09  Inference rules
% 9.13/4.09  ----------------------
% 9.13/4.09  #Ref     : 0
% 9.13/4.09  #Sup     : 3527
% 9.13/4.09  #Fact    : 0
% 9.13/4.09  #Define  : 0
% 9.13/4.09  #Split   : 5
% 9.13/4.09  #Chain   : 0
% 9.13/4.09  #Close   : 0
% 9.13/4.09  
% 9.13/4.09  Ordering : KBO
% 9.13/4.09  
% 9.13/4.09  Simplification rules
% 9.13/4.09  ----------------------
% 9.13/4.09  #Subsume      : 265
% 9.13/4.09  #Demod        : 1756
% 9.13/4.09  #Tautology    : 1703
% 9.13/4.09  #SimpNegUnit  : 114
% 9.13/4.09  #BackRed      : 0
% 9.13/4.09  
% 9.13/4.09  #Partial instantiations: 0
% 9.13/4.09  #Strategies tried      : 1
% 9.13/4.09  
% 9.13/4.09  Timing (in seconds)
% 9.13/4.09  ----------------------
% 9.13/4.09  Preprocessing        : 0.42
% 9.13/4.09  Parsing              : 0.25
% 9.13/4.09  CNF conversion       : 0.02
% 9.13/4.09  Main loop            : 2.83
% 9.13/4.09  Inferencing          : 0.70
% 9.13/4.09  Reduction            : 1.26
% 9.13/4.09  Demodulation         : 1.01
% 9.13/4.09  BG Simplification    : 0.05
% 9.13/4.09  Subsumption          : 0.64
% 9.13/4.09  Abstraction          : 0.07
% 9.13/4.09  MUC search           : 0.00
% 9.13/4.09  Cooper               : 0.00
% 9.13/4.09  Total                : 3.28
% 9.13/4.09  Index Insertion      : 0.00
% 9.13/4.09  Index Deletion       : 0.00
% 9.13/4.09  Index Matching       : 0.00
% 9.13/4.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
