%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:05 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 239 expanded)
%              Number of leaves         :   42 ( 109 expanded)
%              Depth                    :   17
%              Number of atoms          :  181 ( 754 expanded)
%              Number of equality atoms :   25 ( 171 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_wellord1,type,(
    r2_wellord1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
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

tff(f_26,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_149,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_93,axiom,(
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

tff(f_113,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_orders_2(C,A,B)
         => ( v6_orders_2(C,A)
            & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v6_orders_2(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
             => ( m2_orders_2(C,A,B)
              <=> ( C != k1_xboole_0
                  & r2_wellord1(u1_orders_2(A),C)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,C)
                       => k1_funct_1(B,k1_orders_2(A,k3_orders_2(A,C,D))) = D ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_54,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_52,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_50,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_48,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_46,plain,(
    m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_57,plain,(
    ! [A_59] :
      ( k1_xboole_0 = A_59
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_61,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_57])).

tff(c_62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_2])).

tff(c_44,plain,(
    k3_tarski(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_6,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_95,plain,(
    ! [A_63,B_64] :
      ( k3_tarski(A_63) != k1_xboole_0
      | ~ r2_hidden(B_64,A_63)
      | k1_xboole_0 = B_64 ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_112,plain,(
    ! [A_67] :
      ( k3_tarski(A_67) != k1_xboole_0
      | '#skF_1'(A_67) = k1_xboole_0
      | k1_xboole_0 = A_67 ) ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_120,plain,
    ( '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0
    | k4_orders_2('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_112])).

tff(c_122,plain,(
    k4_orders_2('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_104,plain,(
    ! [A_65,B_66] :
      ( ~ v1_xboole_0(k4_orders_2(A_65,B_66))
      | ~ m1_orders_1(B_66,k1_orders_1(u1_struct_0(A_65)))
      | ~ l1_orders_2(A_65)
      | ~ v5_orders_2(A_65)
      | ~ v4_orders_2(A_65)
      | ~ v3_orders_2(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_107,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_104])).

tff(c_110,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_107])).

tff(c_111,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_110])).

tff(c_123,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_111])).

tff(c_127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_123])).

tff(c_129,plain,(
    k4_orders_2('#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_128,plain,(
    '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_133,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7'))
    | k4_orders_2('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_6])).

tff(c_136,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_133])).

tff(c_147,plain,(
    ! [D_75,A_76,B_77] :
      ( m2_orders_2(D_75,A_76,B_77)
      | ~ r2_hidden(D_75,k4_orders_2(A_76,B_77))
      | ~ m1_orders_1(B_77,k1_orders_1(u1_struct_0(A_76)))
      | ~ l1_orders_2(A_76)
      | ~ v5_orders_2(A_76)
      | ~ v4_orders_2(A_76)
      | ~ v3_orders_2(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_149,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_136,c_147])).

tff(c_158,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_149])).

tff(c_159,plain,(
    m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_158])).

tff(c_34,plain,(
    ! [C_51,A_48,B_49] :
      ( v6_orders_2(C_51,A_48)
      | ~ m2_orders_2(C_51,A_48,B_49)
      | ~ m1_orders_1(B_49,k1_orders_1(u1_struct_0(A_48)))
      | ~ l1_orders_2(A_48)
      | ~ v5_orders_2(A_48)
      | ~ v4_orders_2(A_48)
      | ~ v3_orders_2(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_165,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_6')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_159,c_34])).

tff(c_172,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_165])).

tff(c_173,plain,(
    v6_orders_2(k1_xboole_0,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_172])).

tff(c_32,plain,(
    ! [C_51,A_48,B_49] :
      ( m1_subset_1(C_51,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m2_orders_2(C_51,A_48,B_49)
      | ~ m1_orders_1(B_49,k1_orders_1(u1_struct_0(A_48)))
      | ~ l1_orders_2(A_48)
      | ~ v5_orders_2(A_48)
      | ~ v4_orders_2(A_48)
      | ~ v3_orders_2(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_163,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_159,c_32])).

tff(c_168,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_163])).

tff(c_169,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_168])).

tff(c_228,plain,(
    ! [A_87,B_88] :
      ( ~ m2_orders_2(k1_xboole_0,A_87,B_88)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ v6_orders_2(k1_xboole_0,A_87)
      | ~ m1_orders_1(B_88,k1_orders_1(u1_struct_0(A_87)))
      | ~ l1_orders_2(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v4_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_230,plain,(
    ! [B_88] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_88)
      | ~ v6_orders_2(k1_xboole_0,'#skF_6')
      | ~ m1_orders_1(B_88,k1_orders_1(u1_struct_0('#skF_6')))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_169,c_228])).

tff(c_233,plain,(
    ! [B_88] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_88)
      | ~ m1_orders_1(B_88,k1_orders_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_173,c_230])).

tff(c_235,plain,(
    ! [B_89] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_89)
      | ~ m1_orders_1(B_89,k1_orders_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_233])).

tff(c_238,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_235])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:01:34 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.34  
% 2.38/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.34  %$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3
% 2.38/1.34  
% 2.38/1.34  %Foreground sorts:
% 2.38/1.34  
% 2.38/1.34  
% 2.38/1.34  %Background operators:
% 2.38/1.34  
% 2.38/1.34  
% 2.38/1.34  %Foreground operators:
% 2.38/1.34  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.38/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.38/1.34  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.38/1.34  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.38/1.34  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.38/1.34  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.38/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.38/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.34  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.38/1.34  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.38/1.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.38/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.38/1.34  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.38/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.38/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.38/1.34  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.38/1.34  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.38/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.34  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.38/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.38/1.34  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.38/1.34  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.38/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.38/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.38/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.34  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.38/1.34  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.38/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.38/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.34  
% 2.47/1.36  tff(f_167, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.47/1.36  tff(f_26, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 2.47/1.36  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.47/1.36  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.47/1.36  tff(f_149, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 2.47/1.36  tff(f_129, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.47/1.36  tff(f_93, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.47/1.36  tff(f_113, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.47/1.36  tff(f_71, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_orders_2)).
% 2.47/1.36  tff(c_56, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.47/1.36  tff(c_54, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.47/1.36  tff(c_52, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.47/1.36  tff(c_50, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.47/1.36  tff(c_48, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.47/1.36  tff(c_46, plain, (m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.47/1.36  tff(c_2, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.47/1.36  tff(c_57, plain, (![A_59]: (k1_xboole_0=A_59 | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.47/1.36  tff(c_61, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_57])).
% 2.47/1.36  tff(c_62, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_2])).
% 2.47/1.36  tff(c_44, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.47/1.36  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.47/1.36  tff(c_95, plain, (![A_63, B_64]: (k3_tarski(A_63)!=k1_xboole_0 | ~r2_hidden(B_64, A_63) | k1_xboole_0=B_64)), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.47/1.36  tff(c_112, plain, (![A_67]: (k3_tarski(A_67)!=k1_xboole_0 | '#skF_1'(A_67)=k1_xboole_0 | k1_xboole_0=A_67)), inference(resolution, [status(thm)], [c_6, c_95])).
% 2.47/1.36  tff(c_120, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0 | k4_orders_2('#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_44, c_112])).
% 2.47/1.36  tff(c_122, plain, (k4_orders_2('#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_120])).
% 2.47/1.36  tff(c_104, plain, (![A_65, B_66]: (~v1_xboole_0(k4_orders_2(A_65, B_66)) | ~m1_orders_1(B_66, k1_orders_1(u1_struct_0(A_65))) | ~l1_orders_2(A_65) | ~v5_orders_2(A_65) | ~v4_orders_2(A_65) | ~v3_orders_2(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.47/1.36  tff(c_107, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_46, c_104])).
% 2.47/1.36  tff(c_110, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_107])).
% 2.47/1.36  tff(c_111, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_56, c_110])).
% 2.47/1.36  tff(c_123, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_111])).
% 2.47/1.36  tff(c_127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_123])).
% 2.47/1.36  tff(c_129, plain, (k4_orders_2('#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_120])).
% 2.47/1.36  tff(c_128, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_120])).
% 2.47/1.36  tff(c_133, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7')) | k4_orders_2('#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_128, c_6])).
% 2.47/1.36  tff(c_136, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_129, c_133])).
% 2.47/1.36  tff(c_147, plain, (![D_75, A_76, B_77]: (m2_orders_2(D_75, A_76, B_77) | ~r2_hidden(D_75, k4_orders_2(A_76, B_77)) | ~m1_orders_1(B_77, k1_orders_1(u1_struct_0(A_76))) | ~l1_orders_2(A_76) | ~v5_orders_2(A_76) | ~v4_orders_2(A_76) | ~v3_orders_2(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.47/1.36  tff(c_149, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_136, c_147])).
% 2.47/1.36  tff(c_158, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_149])).
% 2.47/1.36  tff(c_159, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_56, c_158])).
% 2.47/1.36  tff(c_34, plain, (![C_51, A_48, B_49]: (v6_orders_2(C_51, A_48) | ~m2_orders_2(C_51, A_48, B_49) | ~m1_orders_1(B_49, k1_orders_1(u1_struct_0(A_48))) | ~l1_orders_2(A_48) | ~v5_orders_2(A_48) | ~v4_orders_2(A_48) | ~v3_orders_2(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.47/1.36  tff(c_165, plain, (v6_orders_2(k1_xboole_0, '#skF_6') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_159, c_34])).
% 2.47/1.36  tff(c_172, plain, (v6_orders_2(k1_xboole_0, '#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_165])).
% 2.47/1.36  tff(c_173, plain, (v6_orders_2(k1_xboole_0, '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_172])).
% 2.47/1.36  tff(c_32, plain, (![C_51, A_48, B_49]: (m1_subset_1(C_51, k1_zfmisc_1(u1_struct_0(A_48))) | ~m2_orders_2(C_51, A_48, B_49) | ~m1_orders_1(B_49, k1_orders_1(u1_struct_0(A_48))) | ~l1_orders_2(A_48) | ~v5_orders_2(A_48) | ~v4_orders_2(A_48) | ~v3_orders_2(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.47/1.36  tff(c_163, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_159, c_32])).
% 2.47/1.36  tff(c_168, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_163])).
% 2.47/1.36  tff(c_169, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_56, c_168])).
% 2.47/1.36  tff(c_228, plain, (![A_87, B_88]: (~m2_orders_2(k1_xboole_0, A_87, B_88) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_87))) | ~v6_orders_2(k1_xboole_0, A_87) | ~m1_orders_1(B_88, k1_orders_1(u1_struct_0(A_87))) | ~l1_orders_2(A_87) | ~v5_orders_2(A_87) | ~v4_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.47/1.36  tff(c_230, plain, (![B_88]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_88) | ~v6_orders_2(k1_xboole_0, '#skF_6') | ~m1_orders_1(B_88, k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_169, c_228])).
% 2.47/1.36  tff(c_233, plain, (![B_88]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_88) | ~m1_orders_1(B_88, k1_orders_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_173, c_230])).
% 2.47/1.36  tff(c_235, plain, (![B_89]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_89) | ~m1_orders_1(B_89, k1_orders_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_233])).
% 2.47/1.36  tff(c_238, plain, (~m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_46, c_235])).
% 2.47/1.36  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_238])).
% 2.47/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.36  
% 2.47/1.36  Inference rules
% 2.47/1.36  ----------------------
% 2.47/1.36  #Ref     : 0
% 2.47/1.36  #Sup     : 35
% 2.47/1.36  #Fact    : 0
% 2.47/1.36  #Define  : 0
% 2.47/1.36  #Split   : 1
% 2.47/1.36  #Chain   : 0
% 2.47/1.36  #Close   : 0
% 2.47/1.36  
% 2.47/1.36  Ordering : KBO
% 2.47/1.36  
% 2.47/1.36  Simplification rules
% 2.47/1.36  ----------------------
% 2.47/1.36  #Subsume      : 0
% 2.47/1.36  #Demod        : 58
% 2.47/1.36  #Tautology    : 18
% 2.47/1.36  #SimpNegUnit  : 11
% 2.47/1.36  #BackRed      : 3
% 2.47/1.36  
% 2.47/1.36  #Partial instantiations: 0
% 2.47/1.36  #Strategies tried      : 1
% 2.47/1.36  
% 2.47/1.36  Timing (in seconds)
% 2.47/1.36  ----------------------
% 2.47/1.36  Preprocessing        : 0.34
% 2.47/1.36  Parsing              : 0.18
% 2.47/1.36  CNF conversion       : 0.03
% 2.47/1.36  Main loop            : 0.19
% 2.47/1.36  Inferencing          : 0.07
% 2.47/1.36  Reduction            : 0.06
% 2.47/1.36  Demodulation         : 0.04
% 2.47/1.36  BG Simplification    : 0.02
% 2.47/1.36  Subsumption          : 0.03
% 2.47/1.36  Abstraction          : 0.01
% 2.47/1.36  MUC search           : 0.00
% 2.47/1.36  Cooper               : 0.00
% 2.47/1.36  Total                : 0.56
% 2.47/1.36  Index Insertion      : 0.00
% 2.47/1.36  Index Deletion       : 0.00
% 2.47/1.36  Index Matching       : 0.00
% 2.47/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
