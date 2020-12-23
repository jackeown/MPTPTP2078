%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:45 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   63 (  76 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  183 ( 250 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_orders_2(A,k1_struct_0(A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_18,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42,plain,(
    ! [A_35] :
      ( k1_struct_0(A_35) = k1_xboole_0
      | ~ l1_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_47,plain,(
    ! [A_36] :
      ( k1_struct_0(A_36) = k1_xboole_0
      | ~ l1_orders_2(A_36) ) ),
    inference(resolution,[status(thm)],[c_18,c_42])).

tff(c_51,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_47])).

tff(c_26,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_52,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_26])).

tff(c_36,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_34,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_32,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_8,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] :
      ( m1_subset_1(k3_orders_2(A_12,B_13,C_14),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_subset_1(C_14,u1_struct_0(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_orders_2(A_12)
      | ~ v5_orders_2(A_12)
      | ~ v4_orders_2(A_12)
      | ~ v3_orders_2(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r2_hidden('#skF_1'(A_2,B_3),B_3)
      | k1_xboole_0 = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_80,plain,(
    ! [A_48,B_49,C_50] :
      ( m1_subset_1(k3_orders_2(A_48,B_49,C_50),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(C_50,u1_struct_0(A_48))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_orders_2(A_48)
      | ~ v5_orders_2(A_48)
      | ~ v4_orders_2(A_48)
      | ~ v3_orders_2(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( m1_subset_1(A_6,C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104,plain,(
    ! [A_59,A_60,B_61,C_62] :
      ( m1_subset_1(A_59,u1_struct_0(A_60))
      | ~ r2_hidden(A_59,k3_orders_2(A_60,B_61,C_62))
      | ~ m1_subset_1(C_62,u1_struct_0(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_orders_2(A_60)
      | ~ v5_orders_2(A_60)
      | ~ v4_orders_2(A_60)
      | ~ v3_orders_2(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_80,c_10])).

tff(c_108,plain,(
    ! [A_2,A_60,B_61,C_62] :
      ( m1_subset_1('#skF_1'(A_2,k3_orders_2(A_60,B_61,C_62)),u1_struct_0(A_60))
      | ~ m1_subset_1(C_62,u1_struct_0(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_orders_2(A_60)
      | ~ v5_orders_2(A_60)
      | ~ v4_orders_2(A_60)
      | ~ v3_orders_2(A_60)
      | v2_struct_0(A_60)
      | k3_orders_2(A_60,B_61,C_62) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_60,B_61,C_62),k1_zfmisc_1(A_2)) ) ),
    inference(resolution,[status(thm)],[c_4,c_104])).

tff(c_109,plain,(
    ! [B_63,D_64,A_65,C_66] :
      ( r2_hidden(B_63,D_64)
      | ~ r2_hidden(B_63,k3_orders_2(A_65,D_64,C_66))
      | ~ m1_subset_1(D_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(C_66,u1_struct_0(A_65))
      | ~ m1_subset_1(B_63,u1_struct_0(A_65))
      | ~ l1_orders_2(A_65)
      | ~ v5_orders_2(A_65)
      | ~ v4_orders_2(A_65)
      | ~ v3_orders_2(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_193,plain,(
    ! [A_107,A_108,D_109,C_110] :
      ( r2_hidden('#skF_1'(A_107,k3_orders_2(A_108,D_109,C_110)),D_109)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(C_110,u1_struct_0(A_108))
      | ~ m1_subset_1('#skF_1'(A_107,k3_orders_2(A_108,D_109,C_110)),u1_struct_0(A_108))
      | ~ l1_orders_2(A_108)
      | ~ v5_orders_2(A_108)
      | ~ v4_orders_2(A_108)
      | ~ v3_orders_2(A_108)
      | v2_struct_0(A_108)
      | k3_orders_2(A_108,D_109,C_110) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_108,D_109,C_110),k1_zfmisc_1(A_107)) ) ),
    inference(resolution,[status(thm)],[c_4,c_109])).

tff(c_201,plain,(
    ! [A_111,A_112,B_113,C_114] :
      ( r2_hidden('#skF_1'(A_111,k3_orders_2(A_112,B_113,C_114)),B_113)
      | ~ m1_subset_1(C_114,u1_struct_0(A_112))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_orders_2(A_112)
      | ~ v5_orders_2(A_112)
      | ~ v4_orders_2(A_112)
      | ~ v3_orders_2(A_112)
      | v2_struct_0(A_112)
      | k3_orders_2(A_112,B_113,C_114) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_112,B_113,C_114),k1_zfmisc_1(A_111)) ) ),
    inference(resolution,[status(thm)],[c_108,c_193])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_252,plain,(
    ! [B_124,A_125,A_126,C_127] :
      ( ~ r1_tarski(B_124,'#skF_1'(A_125,k3_orders_2(A_126,B_124,C_127)))
      | ~ m1_subset_1(C_127,u1_struct_0(A_126))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_orders_2(A_126)
      | ~ v5_orders_2(A_126)
      | ~ v4_orders_2(A_126)
      | ~ v3_orders_2(A_126)
      | v2_struct_0(A_126)
      | k3_orders_2(A_126,B_124,C_127) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_126,B_124,C_127),k1_zfmisc_1(A_125)) ) ),
    inference(resolution,[status(thm)],[c_201,c_12])).

tff(c_256,plain,(
    ! [C_127,A_126,A_125] :
      ( ~ m1_subset_1(C_127,u1_struct_0(A_126))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_orders_2(A_126)
      | ~ v5_orders_2(A_126)
      | ~ v4_orders_2(A_126)
      | ~ v3_orders_2(A_126)
      | v2_struct_0(A_126)
      | k3_orders_2(A_126,k1_xboole_0,C_127) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_126,k1_xboole_0,C_127),k1_zfmisc_1(A_125)) ) ),
    inference(resolution,[status(thm)],[c_2,c_252])).

tff(c_260,plain,(
    ! [C_128,A_129,A_130] :
      ( ~ m1_subset_1(C_128,u1_struct_0(A_129))
      | ~ l1_orders_2(A_129)
      | ~ v5_orders_2(A_129)
      | ~ v4_orders_2(A_129)
      | ~ v3_orders_2(A_129)
      | v2_struct_0(A_129)
      | k3_orders_2(A_129,k1_xboole_0,C_128) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_129,k1_xboole_0,C_128),k1_zfmisc_1(A_130)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_256])).

tff(c_264,plain,(
    ! [A_12,C_14] :
      ( k3_orders_2(A_12,k1_xboole_0,C_14) = k1_xboole_0
      | ~ m1_subset_1(C_14,u1_struct_0(A_12))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_orders_2(A_12)
      | ~ v5_orders_2(A_12)
      | ~ v4_orders_2(A_12)
      | ~ v3_orders_2(A_12)
      | v2_struct_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_260])).

tff(c_268,plain,(
    ! [A_131,C_132] :
      ( k3_orders_2(A_131,k1_xboole_0,C_132) = k1_xboole_0
      | ~ m1_subset_1(C_132,u1_struct_0(A_131))
      | ~ l1_orders_2(A_131)
      | ~ v5_orders_2(A_131)
      | ~ v4_orders_2(A_131)
      | ~ v3_orders_2(A_131)
      | v2_struct_0(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_264])).

tff(c_282,plain,
    ( k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_268])).

tff(c_288,plain,
    ( k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_282])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_52,c_288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.40  
% 2.78/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.40  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.78/1.40  
% 2.78/1.40  %Foreground sorts:
% 2.78/1.40  
% 2.78/1.40  
% 2.78/1.40  %Background operators:
% 2.78/1.40  
% 2.78/1.40  
% 2.78/1.40  %Foreground operators:
% 2.78/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.78/1.40  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.40  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.78/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.40  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.78/1.40  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.78/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.78/1.40  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.40  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.78/1.40  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.78/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.78/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.78/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.40  
% 2.78/1.42  tff(f_120, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_orders_2)).
% 2.78/1.42  tff(f_77, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.78/1.42  tff(f_56, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 2.78/1.42  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.78/1.42  tff(f_73, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.78/1.42  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.78/1.42  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 2.78/1.42  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.78/1.42  tff(f_103, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 2.78/1.42  tff(f_52, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.78/1.42  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.78/1.42  tff(c_30, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.78/1.42  tff(c_18, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.78/1.42  tff(c_42, plain, (![A_35]: (k1_struct_0(A_35)=k1_xboole_0 | ~l1_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.78/1.42  tff(c_47, plain, (![A_36]: (k1_struct_0(A_36)=k1_xboole_0 | ~l1_orders_2(A_36))), inference(resolution, [status(thm)], [c_18, c_42])).
% 2.78/1.42  tff(c_51, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_47])).
% 2.78/1.42  tff(c_26, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.78/1.42  tff(c_52, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_51, c_26])).
% 2.78/1.42  tff(c_36, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.78/1.42  tff(c_34, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.78/1.42  tff(c_32, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.78/1.42  tff(c_28, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.78/1.42  tff(c_8, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.42  tff(c_16, plain, (![A_12, B_13, C_14]: (m1_subset_1(k3_orders_2(A_12, B_13, C_14), k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_subset_1(C_14, u1_struct_0(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_orders_2(A_12) | ~v5_orders_2(A_12) | ~v4_orders_2(A_12) | ~v3_orders_2(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.78/1.42  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.78/1.42  tff(c_4, plain, (![A_2, B_3]: (r2_hidden('#skF_1'(A_2, B_3), B_3) | k1_xboole_0=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.78/1.42  tff(c_80, plain, (![A_48, B_49, C_50]: (m1_subset_1(k3_orders_2(A_48, B_49, C_50), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_subset_1(C_50, u1_struct_0(A_48)) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_orders_2(A_48) | ~v5_orders_2(A_48) | ~v4_orders_2(A_48) | ~v3_orders_2(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.78/1.42  tff(c_10, plain, (![A_6, C_8, B_7]: (m1_subset_1(A_6, C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.78/1.42  tff(c_104, plain, (![A_59, A_60, B_61, C_62]: (m1_subset_1(A_59, u1_struct_0(A_60)) | ~r2_hidden(A_59, k3_orders_2(A_60, B_61, C_62)) | ~m1_subset_1(C_62, u1_struct_0(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_orders_2(A_60) | ~v5_orders_2(A_60) | ~v4_orders_2(A_60) | ~v3_orders_2(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_80, c_10])).
% 2.78/1.42  tff(c_108, plain, (![A_2, A_60, B_61, C_62]: (m1_subset_1('#skF_1'(A_2, k3_orders_2(A_60, B_61, C_62)), u1_struct_0(A_60)) | ~m1_subset_1(C_62, u1_struct_0(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_orders_2(A_60) | ~v5_orders_2(A_60) | ~v4_orders_2(A_60) | ~v3_orders_2(A_60) | v2_struct_0(A_60) | k3_orders_2(A_60, B_61, C_62)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_60, B_61, C_62), k1_zfmisc_1(A_2)))), inference(resolution, [status(thm)], [c_4, c_104])).
% 2.78/1.42  tff(c_109, plain, (![B_63, D_64, A_65, C_66]: (r2_hidden(B_63, D_64) | ~r2_hidden(B_63, k3_orders_2(A_65, D_64, C_66)) | ~m1_subset_1(D_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_subset_1(C_66, u1_struct_0(A_65)) | ~m1_subset_1(B_63, u1_struct_0(A_65)) | ~l1_orders_2(A_65) | ~v5_orders_2(A_65) | ~v4_orders_2(A_65) | ~v3_orders_2(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.78/1.42  tff(c_193, plain, (![A_107, A_108, D_109, C_110]: (r2_hidden('#skF_1'(A_107, k3_orders_2(A_108, D_109, C_110)), D_109) | ~m1_subset_1(D_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(C_110, u1_struct_0(A_108)) | ~m1_subset_1('#skF_1'(A_107, k3_orders_2(A_108, D_109, C_110)), u1_struct_0(A_108)) | ~l1_orders_2(A_108) | ~v5_orders_2(A_108) | ~v4_orders_2(A_108) | ~v3_orders_2(A_108) | v2_struct_0(A_108) | k3_orders_2(A_108, D_109, C_110)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_108, D_109, C_110), k1_zfmisc_1(A_107)))), inference(resolution, [status(thm)], [c_4, c_109])).
% 2.78/1.42  tff(c_201, plain, (![A_111, A_112, B_113, C_114]: (r2_hidden('#skF_1'(A_111, k3_orders_2(A_112, B_113, C_114)), B_113) | ~m1_subset_1(C_114, u1_struct_0(A_112)) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_orders_2(A_112) | ~v5_orders_2(A_112) | ~v4_orders_2(A_112) | ~v3_orders_2(A_112) | v2_struct_0(A_112) | k3_orders_2(A_112, B_113, C_114)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_112, B_113, C_114), k1_zfmisc_1(A_111)))), inference(resolution, [status(thm)], [c_108, c_193])).
% 2.78/1.42  tff(c_12, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.78/1.42  tff(c_252, plain, (![B_124, A_125, A_126, C_127]: (~r1_tarski(B_124, '#skF_1'(A_125, k3_orders_2(A_126, B_124, C_127))) | ~m1_subset_1(C_127, u1_struct_0(A_126)) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_orders_2(A_126) | ~v5_orders_2(A_126) | ~v4_orders_2(A_126) | ~v3_orders_2(A_126) | v2_struct_0(A_126) | k3_orders_2(A_126, B_124, C_127)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_126, B_124, C_127), k1_zfmisc_1(A_125)))), inference(resolution, [status(thm)], [c_201, c_12])).
% 2.78/1.42  tff(c_256, plain, (![C_127, A_126, A_125]: (~m1_subset_1(C_127, u1_struct_0(A_126)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_orders_2(A_126) | ~v5_orders_2(A_126) | ~v4_orders_2(A_126) | ~v3_orders_2(A_126) | v2_struct_0(A_126) | k3_orders_2(A_126, k1_xboole_0, C_127)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_126, k1_xboole_0, C_127), k1_zfmisc_1(A_125)))), inference(resolution, [status(thm)], [c_2, c_252])).
% 2.78/1.42  tff(c_260, plain, (![C_128, A_129, A_130]: (~m1_subset_1(C_128, u1_struct_0(A_129)) | ~l1_orders_2(A_129) | ~v5_orders_2(A_129) | ~v4_orders_2(A_129) | ~v3_orders_2(A_129) | v2_struct_0(A_129) | k3_orders_2(A_129, k1_xboole_0, C_128)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_129, k1_xboole_0, C_128), k1_zfmisc_1(A_130)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_256])).
% 2.78/1.42  tff(c_264, plain, (![A_12, C_14]: (k3_orders_2(A_12, k1_xboole_0, C_14)=k1_xboole_0 | ~m1_subset_1(C_14, u1_struct_0(A_12)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_orders_2(A_12) | ~v5_orders_2(A_12) | ~v4_orders_2(A_12) | ~v3_orders_2(A_12) | v2_struct_0(A_12))), inference(resolution, [status(thm)], [c_16, c_260])).
% 2.78/1.42  tff(c_268, plain, (![A_131, C_132]: (k3_orders_2(A_131, k1_xboole_0, C_132)=k1_xboole_0 | ~m1_subset_1(C_132, u1_struct_0(A_131)) | ~l1_orders_2(A_131) | ~v5_orders_2(A_131) | ~v4_orders_2(A_131) | ~v3_orders_2(A_131) | v2_struct_0(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_264])).
% 2.78/1.42  tff(c_282, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_268])).
% 2.78/1.42  tff(c_288, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_282])).
% 2.78/1.42  tff(c_290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_52, c_288])).
% 2.78/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.42  
% 2.78/1.42  Inference rules
% 2.78/1.42  ----------------------
% 2.78/1.42  #Ref     : 0
% 2.78/1.42  #Sup     : 51
% 2.78/1.42  #Fact    : 0
% 2.78/1.42  #Define  : 0
% 2.78/1.42  #Split   : 0
% 2.78/1.42  #Chain   : 0
% 2.78/1.42  #Close   : 0
% 2.78/1.42  
% 2.78/1.42  Ordering : KBO
% 2.78/1.42  
% 2.78/1.42  Simplification rules
% 2.78/1.42  ----------------------
% 2.78/1.42  #Subsume      : 7
% 2.78/1.42  #Demod        : 13
% 2.78/1.42  #Tautology    : 10
% 2.78/1.42  #SimpNegUnit  : 1
% 2.78/1.42  #BackRed      : 1
% 2.78/1.42  
% 2.78/1.42  #Partial instantiations: 0
% 2.78/1.42  #Strategies tried      : 1
% 2.78/1.42  
% 2.78/1.42  Timing (in seconds)
% 2.78/1.42  ----------------------
% 2.78/1.42  Preprocessing        : 0.31
% 2.78/1.42  Parsing              : 0.17
% 2.78/1.42  CNF conversion       : 0.02
% 2.78/1.42  Main loop            : 0.33
% 2.78/1.42  Inferencing          : 0.14
% 2.78/1.42  Reduction            : 0.08
% 2.78/1.42  Demodulation         : 0.05
% 2.78/1.42  BG Simplification    : 0.02
% 2.78/1.42  Subsumption          : 0.07
% 2.78/1.42  Abstraction          : 0.01
% 2.78/1.42  MUC search           : 0.00
% 2.78/1.42  Cooper               : 0.00
% 2.78/1.42  Total                : 0.67
% 2.78/1.42  Index Insertion      : 0.00
% 2.78/1.42  Index Deletion       : 0.00
% 2.78/1.42  Index Matching       : 0.00
% 2.78/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
