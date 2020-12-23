%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:03 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 211 expanded)
%              Number of leaves         :   39 (  94 expanded)
%              Depth                    :   13
%              Number of atoms          :  176 ( 570 expanded)
%              Number of equality atoms :   14 (  62 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_32,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( C = k4_orders_2(A,B)
            <=> ! [D] :
                  ( r2_hidden(D,C)
                <=> m2_orders_2(D,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_xboole_0(C,B) )
     => r1_xboole_0(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => ! [D] :
                  ( m2_orders_2(D,A,B)
                 => ~ r1_xboole_0(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_50,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_48,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_44,plain,(
    m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_6,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_67,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6])).

tff(c_161,plain,(
    ! [A_75,B_76] :
      ( m2_orders_2('#skF_5'(A_75,B_76),A_75,B_76)
      | ~ m1_orders_1(B_76,k1_orders_1(u1_struct_0(A_75)))
      | ~ l1_orders_2(A_75)
      | ~ v5_orders_2(A_75)
      | ~ v4_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_163,plain,
    ( m2_orders_2('#skF_5'('#skF_6','#skF_7'),'#skF_6','#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_161])).

tff(c_166,plain,
    ( m2_orders_2('#skF_5'('#skF_6','#skF_7'),'#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_163])).

tff(c_167,plain,(
    m2_orders_2('#skF_5'('#skF_6','#skF_7'),'#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_166])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    k3_tarski(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_87,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,k3_tarski(B_62))
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_114,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,k1_xboole_0)
      | ~ r2_hidden(A_66,k4_orders_2('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_87])).

tff(c_119,plain,
    ( r1_tarski('#skF_1'(k4_orders_2('#skF_6','#skF_7')),k1_xboole_0)
    | v1_xboole_0(k4_orders_2('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_4,c_114])).

tff(c_170,plain,(
    v1_xboole_0(k4_orders_2('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_174,plain,(
    k4_orders_2('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_170,c_8])).

tff(c_234,plain,(
    ! [D_86,A_87,B_88] :
      ( r2_hidden(D_86,k4_orders_2(A_87,B_88))
      | ~ m2_orders_2(D_86,A_87,B_88)
      | ~ m1_orders_1(B_88,k1_orders_1(u1_struct_0(A_87)))
      | ~ l1_orders_2(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v4_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_236,plain,(
    ! [D_86] :
      ( r2_hidden(D_86,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_86,'#skF_6','#skF_7')
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_44,c_234])).

tff(c_239,plain,(
    ! [D_86] :
      ( r2_hidden(D_86,k1_xboole_0)
      | ~ m2_orders_2(D_86,'#skF_6','#skF_7')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_174,c_236])).

tff(c_241,plain,(
    ! [D_89] :
      ( r2_hidden(D_89,k1_xboole_0)
      | ~ m2_orders_2(D_89,'#skF_6','#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_239])).

tff(c_249,plain,(
    r2_hidden('#skF_5'('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_167,c_241])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_258,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_249,c_2])).

tff(c_264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_258])).

tff(c_266,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_265,plain,(
    r1_tarski('#skF_1'(k4_orders_2('#skF_6','#skF_7')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_101,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_109,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_101])).

tff(c_272,plain,(
    '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_265,c_109])).

tff(c_281,plain,
    ( v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_4])).

tff(c_284,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_281])).

tff(c_26,plain,(
    ! [D_35,A_14,B_26] :
      ( m2_orders_2(D_35,A_14,B_26)
      | ~ r2_hidden(D_35,k4_orders_2(A_14,B_26))
      | ~ m1_orders_1(B_26,k1_orders_1(u1_struct_0(A_14)))
      | ~ l1_orders_2(A_14)
      | ~ v5_orders_2(A_14)
      | ~ v4_orders_2(A_14)
      | ~ v3_orders_2(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_297,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_284,c_26])).

tff(c_306,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_297])).

tff(c_307,plain,(
    m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_306])).

tff(c_20,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_134,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_2'(A_70,B_71),A_70)
      | r1_xboole_0(k3_tarski(A_70),B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_151,plain,(
    ! [A_72,B_73] :
      ( ~ v1_xboole_0(A_72)
      | r1_xboole_0(k3_tarski(A_72),B_73) ) ),
    inference(resolution,[status(thm)],[c_134,c_2])).

tff(c_157,plain,(
    ! [B_73] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,B_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_151])).

tff(c_159,plain,(
    ! [B_73] : r1_xboole_0(k1_xboole_0,B_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_157])).

tff(c_404,plain,(
    ! [C_103,D_104,A_105,B_106] :
      ( ~ r1_xboole_0(C_103,D_104)
      | ~ m2_orders_2(D_104,A_105,B_106)
      | ~ m2_orders_2(C_103,A_105,B_106)
      | ~ m1_orders_1(B_106,k1_orders_1(u1_struct_0(A_105)))
      | ~ l1_orders_2(A_105)
      | ~ v5_orders_2(A_105)
      | ~ v4_orders_2(A_105)
      | ~ v3_orders_2(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_433,plain,(
    ! [B_109,A_110,B_111] :
      ( ~ m2_orders_2(B_109,A_110,B_111)
      | ~ m2_orders_2(k1_xboole_0,A_110,B_111)
      | ~ m1_orders_1(B_111,k1_orders_1(u1_struct_0(A_110)))
      | ~ l1_orders_2(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v4_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_159,c_404])).

tff(c_435,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_307,c_433])).

tff(c_438,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_307,c_435])).

tff(c_440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:36:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.35  
% 2.25/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.35  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5
% 2.59/1.35  
% 2.59/1.35  %Foreground sorts:
% 2.59/1.35  
% 2.59/1.35  
% 2.59/1.35  %Background operators:
% 2.59/1.35  
% 2.59/1.35  
% 2.59/1.35  %Foreground operators:
% 2.59/1.35  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.59/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.59/1.35  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.59/1.35  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.59/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.35  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.59/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.59/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.59/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.35  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.59/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.59/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.59/1.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.59/1.35  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.59/1.35  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.59/1.35  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.59/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.59/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.59/1.35  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.59/1.35  
% 2.59/1.36  tff(f_135, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.59/1.36  tff(f_32, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 2.59/1.36  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.59/1.36  tff(f_94, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 2.59/1.36  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.59/1.36  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.59/1.36  tff(f_78, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.59/1.36  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.59/1.36  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.59/1.36  tff(f_49, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.59/1.36  tff(f_56, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_xboole_0(C, B))) => r1_xboole_0(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 2.59/1.36  tff(f_117, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 2.59/1.36  tff(c_54, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.59/1.36  tff(c_52, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.59/1.36  tff(c_50, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.59/1.36  tff(c_48, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.59/1.36  tff(c_46, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.59/1.36  tff(c_44, plain, (m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.59/1.36  tff(c_6, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.36  tff(c_62, plain, (![A_57]: (k1_xboole_0=A_57 | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.59/1.36  tff(c_66, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_62])).
% 2.59/1.36  tff(c_67, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6])).
% 2.59/1.36  tff(c_161, plain, (![A_75, B_76]: (m2_orders_2('#skF_5'(A_75, B_76), A_75, B_76) | ~m1_orders_1(B_76, k1_orders_1(u1_struct_0(A_75))) | ~l1_orders_2(A_75) | ~v5_orders_2(A_75) | ~v4_orders_2(A_75) | ~v3_orders_2(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.59/1.36  tff(c_163, plain, (m2_orders_2('#skF_5'('#skF_6', '#skF_7'), '#skF_6', '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_44, c_161])).
% 2.59/1.36  tff(c_166, plain, (m2_orders_2('#skF_5'('#skF_6', '#skF_7'), '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_163])).
% 2.59/1.36  tff(c_167, plain, (m2_orders_2('#skF_5'('#skF_6', '#skF_7'), '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_54, c_166])).
% 2.59/1.36  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.36  tff(c_42, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.59/1.36  tff(c_87, plain, (![A_61, B_62]: (r1_tarski(A_61, k3_tarski(B_62)) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.59/1.36  tff(c_114, plain, (![A_66]: (r1_tarski(A_66, k1_xboole_0) | ~r2_hidden(A_66, k4_orders_2('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_87])).
% 2.59/1.36  tff(c_119, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_6', '#skF_7')), k1_xboole_0) | v1_xboole_0(k4_orders_2('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_4, c_114])).
% 2.59/1.36  tff(c_170, plain, (v1_xboole_0(k4_orders_2('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_119])).
% 2.59/1.36  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.59/1.36  tff(c_174, plain, (k4_orders_2('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_170, c_8])).
% 2.59/1.36  tff(c_234, plain, (![D_86, A_87, B_88]: (r2_hidden(D_86, k4_orders_2(A_87, B_88)) | ~m2_orders_2(D_86, A_87, B_88) | ~m1_orders_1(B_88, k1_orders_1(u1_struct_0(A_87))) | ~l1_orders_2(A_87) | ~v5_orders_2(A_87) | ~v4_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.59/1.36  tff(c_236, plain, (![D_86]: (r2_hidden(D_86, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_86, '#skF_6', '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_234])).
% 2.59/1.36  tff(c_239, plain, (![D_86]: (r2_hidden(D_86, k1_xboole_0) | ~m2_orders_2(D_86, '#skF_6', '#skF_7') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_174, c_236])).
% 2.59/1.36  tff(c_241, plain, (![D_89]: (r2_hidden(D_89, k1_xboole_0) | ~m2_orders_2(D_89, '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_54, c_239])).
% 2.59/1.36  tff(c_249, plain, (r2_hidden('#skF_5'('#skF_6', '#skF_7'), k1_xboole_0)), inference(resolution, [status(thm)], [c_167, c_241])).
% 2.59/1.36  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.36  tff(c_258, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_249, c_2])).
% 2.59/1.36  tff(c_264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_258])).
% 2.59/1.36  tff(c_266, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_119])).
% 2.59/1.36  tff(c_265, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_6', '#skF_7')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_119])).
% 2.59/1.36  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.59/1.36  tff(c_101, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.59/1.36  tff(c_109, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_101])).
% 2.59/1.36  tff(c_272, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_265, c_109])).
% 2.59/1.36  tff(c_281, plain, (v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_272, c_4])).
% 2.59/1.36  tff(c_284, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_266, c_281])).
% 2.59/1.36  tff(c_26, plain, (![D_35, A_14, B_26]: (m2_orders_2(D_35, A_14, B_26) | ~r2_hidden(D_35, k4_orders_2(A_14, B_26)) | ~m1_orders_1(B_26, k1_orders_1(u1_struct_0(A_14))) | ~l1_orders_2(A_14) | ~v5_orders_2(A_14) | ~v4_orders_2(A_14) | ~v3_orders_2(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.59/1.36  tff(c_297, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_284, c_26])).
% 2.59/1.36  tff(c_306, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_297])).
% 2.59/1.36  tff(c_307, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_54, c_306])).
% 2.59/1.36  tff(c_20, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.59/1.36  tff(c_134, plain, (![A_70, B_71]: (r2_hidden('#skF_2'(A_70, B_71), A_70) | r1_xboole_0(k3_tarski(A_70), B_71))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.59/1.36  tff(c_151, plain, (![A_72, B_73]: (~v1_xboole_0(A_72) | r1_xboole_0(k3_tarski(A_72), B_73))), inference(resolution, [status(thm)], [c_134, c_2])).
% 2.59/1.36  tff(c_157, plain, (![B_73]: (~v1_xboole_0(k1_xboole_0) | r1_xboole_0(k1_xboole_0, B_73))), inference(superposition, [status(thm), theory('equality')], [c_20, c_151])).
% 2.59/1.36  tff(c_159, plain, (![B_73]: (r1_xboole_0(k1_xboole_0, B_73))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_157])).
% 2.59/1.36  tff(c_404, plain, (![C_103, D_104, A_105, B_106]: (~r1_xboole_0(C_103, D_104) | ~m2_orders_2(D_104, A_105, B_106) | ~m2_orders_2(C_103, A_105, B_106) | ~m1_orders_1(B_106, k1_orders_1(u1_struct_0(A_105))) | ~l1_orders_2(A_105) | ~v5_orders_2(A_105) | ~v4_orders_2(A_105) | ~v3_orders_2(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.59/1.36  tff(c_433, plain, (![B_109, A_110, B_111]: (~m2_orders_2(B_109, A_110, B_111) | ~m2_orders_2(k1_xboole_0, A_110, B_111) | ~m1_orders_1(B_111, k1_orders_1(u1_struct_0(A_110))) | ~l1_orders_2(A_110) | ~v5_orders_2(A_110) | ~v4_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110))), inference(resolution, [status(thm)], [c_159, c_404])).
% 2.59/1.36  tff(c_435, plain, (~m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_307, c_433])).
% 2.59/1.36  tff(c_438, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_307, c_435])).
% 2.59/1.36  tff(c_440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_438])).
% 2.59/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.36  
% 2.59/1.36  Inference rules
% 2.59/1.36  ----------------------
% 2.59/1.36  #Ref     : 0
% 2.59/1.36  #Sup     : 77
% 2.59/1.36  #Fact    : 0
% 2.59/1.36  #Define  : 0
% 2.59/1.36  #Split   : 1
% 2.59/1.36  #Chain   : 0
% 2.59/1.36  #Close   : 0
% 2.59/1.36  
% 2.59/1.36  Ordering : KBO
% 2.59/1.36  
% 2.59/1.36  Simplification rules
% 2.59/1.36  ----------------------
% 2.59/1.36  #Subsume      : 7
% 2.59/1.36  #Demod        : 80
% 2.59/1.36  #Tautology    : 42
% 2.59/1.36  #SimpNegUnit  : 9
% 2.59/1.36  #BackRed      : 6
% 2.59/1.37  
% 2.59/1.37  #Partial instantiations: 0
% 2.59/1.37  #Strategies tried      : 1
% 2.59/1.37  
% 2.59/1.37  Timing (in seconds)
% 2.59/1.37  ----------------------
% 2.59/1.37  Preprocessing        : 0.32
% 2.59/1.37  Parsing              : 0.17
% 2.59/1.37  CNF conversion       : 0.03
% 2.59/1.37  Main loop            : 0.26
% 2.59/1.37  Inferencing          : 0.09
% 2.59/1.37  Reduction            : 0.08
% 2.59/1.37  Demodulation         : 0.06
% 2.59/1.37  BG Simplification    : 0.02
% 2.59/1.37  Subsumption          : 0.05
% 2.59/1.37  Abstraction          : 0.01
% 2.59/1.37  MUC search           : 0.00
% 2.59/1.37  Cooper               : 0.00
% 2.59/1.37  Total                : 0.62
% 2.59/1.37  Index Insertion      : 0.00
% 2.59/1.37  Index Deletion       : 0.00
% 2.59/1.37  Index Matching       : 0.00
% 2.59/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
