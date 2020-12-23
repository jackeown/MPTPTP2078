%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:05 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 277 expanded)
%              Number of leaves         :   39 ( 128 expanded)
%              Depth                    :   19
%              Number of atoms          :  169 ( 989 expanded)
%              Number of equality atoms :   16 ( 116 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(f_160,negated_conjecture,(
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

tff(f_122,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_142,axiom,(
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

tff(f_86,axiom,(
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

tff(f_106,axiom,(
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

tff(f_64,axiom,(
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

tff(c_54,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_52,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_50,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_48,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_46,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_44,plain,(
    m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_102,plain,(
    ! [A_69,B_70] :
      ( ~ v1_xboole_0(k4_orders_2(A_69,B_70))
      | ~ m1_orders_1(B_70,k1_orders_1(u1_struct_0(A_69)))
      | ~ l1_orders_2(A_69)
      | ~ v5_orders_2(A_69)
      | ~ v4_orders_2(A_69)
      | ~ v3_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_105,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_102])).

tff(c_108,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_105])).

tff(c_109,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_108])).

tff(c_42,plain,(
    k3_tarski(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [A_66,B_67] :
      ( k3_tarski(A_66) != k1_xboole_0
      | ~ r2_hidden(B_67,A_66)
      | k1_xboole_0 = B_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_96,plain,(
    ! [A_1] :
      ( k3_tarski(A_1) != k1_xboole_0
      | '#skF_1'(A_1) = k1_xboole_0
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_88])).

tff(c_113,plain,
    ( k3_tarski(k4_orders_2('#skF_6','#skF_7')) != k1_xboole_0
    | '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_96,c_109])).

tff(c_116,plain,(
    '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_113])).

tff(c_120,plain,
    ( v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_4])).

tff(c_123,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_120])).

tff(c_137,plain,(
    ! [D_77,A_78,B_79] :
      ( m2_orders_2(D_77,A_78,B_79)
      | ~ r2_hidden(D_77,k4_orders_2(A_78,B_79))
      | ~ m1_orders_1(B_79,k1_orders_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_139,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_123,c_137])).

tff(c_148,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_139])).

tff(c_149,plain,(
    m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_148])).

tff(c_32,plain,(
    ! [C_52,A_49,B_50] :
      ( v6_orders_2(C_52,A_49)
      | ~ m2_orders_2(C_52,A_49,B_50)
      | ~ m1_orders_1(B_50,k1_orders_1(u1_struct_0(A_49)))
      | ~ l1_orders_2(A_49)
      | ~ v5_orders_2(A_49)
      | ~ v4_orders_2(A_49)
      | ~ v3_orders_2(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_155,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_6')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_149,c_32])).

tff(c_162,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_155])).

tff(c_163,plain,(
    v6_orders_2(k1_xboole_0,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_162])).

tff(c_30,plain,(
    ! [C_52,A_49,B_50] :
      ( m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m2_orders_2(C_52,A_49,B_50)
      | ~ m1_orders_1(B_50,k1_orders_1(u1_struct_0(A_49)))
      | ~ l1_orders_2(A_49)
      | ~ v5_orders_2(A_49)
      | ~ v4_orders_2(A_49)
      | ~ v3_orders_2(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_153,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_149,c_30])).

tff(c_158,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_153])).

tff(c_159,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_158])).

tff(c_171,plain,(
    ! [A_83,B_84] :
      ( ~ m2_orders_2(k1_xboole_0,A_83,B_84)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ v6_orders_2(k1_xboole_0,A_83)
      | ~ m1_orders_1(B_84,k1_orders_1(u1_struct_0(A_83)))
      | ~ l1_orders_2(A_83)
      | ~ v5_orders_2(A_83)
      | ~ v4_orders_2(A_83)
      | ~ v3_orders_2(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_173,plain,(
    ! [B_84] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_84)
      | ~ v6_orders_2(k1_xboole_0,'#skF_6')
      | ~ m1_orders_1(B_84,k1_orders_1(u1_struct_0('#skF_6')))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_159,c_171])).

tff(c_176,plain,(
    ! [B_84] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_84)
      | ~ m1_orders_1(B_84,k1_orders_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_163,c_173])).

tff(c_201,plain,(
    ! [B_87] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_87)
      | ~ m1_orders_1(B_87,k1_orders_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_176])).

tff(c_204,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_201])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:15:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.26  
% 2.18/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.26  %$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3
% 2.18/1.26  
% 2.18/1.26  %Foreground sorts:
% 2.18/1.26  
% 2.18/1.26  
% 2.18/1.26  %Background operators:
% 2.18/1.26  
% 2.18/1.26  
% 2.18/1.26  %Foreground operators:
% 2.18/1.26  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.18/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.18/1.26  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.18/1.26  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.18/1.26  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.18/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.26  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.18/1.26  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.18/1.26  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.18/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.18/1.26  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.18/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.18/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.18/1.26  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.18/1.26  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.18/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.26  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.18/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.18/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.18/1.26  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.18/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.26  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.18/1.26  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.18/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.26  
% 2.29/1.27  tff(f_160, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.29/1.27  tff(f_122, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.29/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.29/1.27  tff(f_142, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 2.29/1.27  tff(f_86, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.29/1.27  tff(f_106, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.29/1.27  tff(f_64, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_orders_2)).
% 2.29/1.27  tff(c_54, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.29/1.27  tff(c_52, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.29/1.27  tff(c_50, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.29/1.27  tff(c_48, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.29/1.27  tff(c_46, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.29/1.27  tff(c_44, plain, (m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.29/1.27  tff(c_102, plain, (![A_69, B_70]: (~v1_xboole_0(k4_orders_2(A_69, B_70)) | ~m1_orders_1(B_70, k1_orders_1(u1_struct_0(A_69))) | ~l1_orders_2(A_69) | ~v5_orders_2(A_69) | ~v4_orders_2(A_69) | ~v3_orders_2(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.29/1.27  tff(c_105, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_44, c_102])).
% 2.29/1.27  tff(c_108, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_105])).
% 2.29/1.27  tff(c_109, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_54, c_108])).
% 2.29/1.27  tff(c_42, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.29/1.27  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.27  tff(c_88, plain, (![A_66, B_67]: (k3_tarski(A_66)!=k1_xboole_0 | ~r2_hidden(B_67, A_66) | k1_xboole_0=B_67)), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.29/1.27  tff(c_96, plain, (![A_1]: (k3_tarski(A_1)!=k1_xboole_0 | '#skF_1'(A_1)=k1_xboole_0 | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_88])).
% 2.29/1.27  tff(c_113, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))!=k1_xboole_0 | '#skF_1'(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_96, c_109])).
% 2.29/1.27  tff(c_116, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_113])).
% 2.29/1.27  tff(c_120, plain, (v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_4])).
% 2.29/1.27  tff(c_123, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_109, c_120])).
% 2.29/1.27  tff(c_137, plain, (![D_77, A_78, B_79]: (m2_orders_2(D_77, A_78, B_79) | ~r2_hidden(D_77, k4_orders_2(A_78, B_79)) | ~m1_orders_1(B_79, k1_orders_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.29/1.27  tff(c_139, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_123, c_137])).
% 2.29/1.27  tff(c_148, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_139])).
% 2.29/1.27  tff(c_149, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_54, c_148])).
% 2.29/1.27  tff(c_32, plain, (![C_52, A_49, B_50]: (v6_orders_2(C_52, A_49) | ~m2_orders_2(C_52, A_49, B_50) | ~m1_orders_1(B_50, k1_orders_1(u1_struct_0(A_49))) | ~l1_orders_2(A_49) | ~v5_orders_2(A_49) | ~v4_orders_2(A_49) | ~v3_orders_2(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.29/1.27  tff(c_155, plain, (v6_orders_2(k1_xboole_0, '#skF_6') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_149, c_32])).
% 2.29/1.27  tff(c_162, plain, (v6_orders_2(k1_xboole_0, '#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_155])).
% 2.29/1.27  tff(c_163, plain, (v6_orders_2(k1_xboole_0, '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_54, c_162])).
% 2.29/1.27  tff(c_30, plain, (![C_52, A_49, B_50]: (m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(A_49))) | ~m2_orders_2(C_52, A_49, B_50) | ~m1_orders_1(B_50, k1_orders_1(u1_struct_0(A_49))) | ~l1_orders_2(A_49) | ~v5_orders_2(A_49) | ~v4_orders_2(A_49) | ~v3_orders_2(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.29/1.27  tff(c_153, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_149, c_30])).
% 2.29/1.27  tff(c_158, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_153])).
% 2.29/1.27  tff(c_159, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_54, c_158])).
% 2.29/1.27  tff(c_171, plain, (![A_83, B_84]: (~m2_orders_2(k1_xboole_0, A_83, B_84) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_83))) | ~v6_orders_2(k1_xboole_0, A_83) | ~m1_orders_1(B_84, k1_orders_1(u1_struct_0(A_83))) | ~l1_orders_2(A_83) | ~v5_orders_2(A_83) | ~v4_orders_2(A_83) | ~v3_orders_2(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.29/1.27  tff(c_173, plain, (![B_84]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_84) | ~v6_orders_2(k1_xboole_0, '#skF_6') | ~m1_orders_1(B_84, k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_159, c_171])).
% 2.29/1.27  tff(c_176, plain, (![B_84]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_84) | ~m1_orders_1(B_84, k1_orders_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_163, c_173])).
% 2.29/1.27  tff(c_201, plain, (![B_87]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_87) | ~m1_orders_1(B_87, k1_orders_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_176])).
% 2.29/1.27  tff(c_204, plain, (~m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_44, c_201])).
% 2.29/1.27  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_204])).
% 2.29/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.27  
% 2.29/1.27  Inference rules
% 2.29/1.27  ----------------------
% 2.29/1.27  #Ref     : 0
% 2.29/1.27  #Sup     : 30
% 2.29/1.27  #Fact    : 0
% 2.29/1.27  #Define  : 0
% 2.29/1.27  #Split   : 0
% 2.29/1.27  #Chain   : 0
% 2.29/1.27  #Close   : 0
% 2.29/1.27  
% 2.29/1.27  Ordering : KBO
% 2.29/1.27  
% 2.29/1.27  Simplification rules
% 2.29/1.27  ----------------------
% 2.29/1.27  #Subsume      : 2
% 2.29/1.27  #Demod        : 37
% 2.29/1.27  #Tautology    : 14
% 2.29/1.27  #SimpNegUnit  : 8
% 2.29/1.27  #BackRed      : 0
% 2.29/1.27  
% 2.29/1.27  #Partial instantiations: 0
% 2.29/1.27  #Strategies tried      : 1
% 2.29/1.27  
% 2.29/1.27  Timing (in seconds)
% 2.29/1.27  ----------------------
% 2.29/1.28  Preprocessing        : 0.33
% 2.29/1.28  Parsing              : 0.17
% 2.29/1.28  CNF conversion       : 0.03
% 2.29/1.28  Main loop            : 0.17
% 2.29/1.28  Inferencing          : 0.06
% 2.29/1.28  Reduction            : 0.05
% 2.29/1.28  Demodulation         : 0.04
% 2.29/1.28  BG Simplification    : 0.02
% 2.29/1.28  Subsumption          : 0.03
% 2.29/1.28  Abstraction          : 0.01
% 2.29/1.28  MUC search           : 0.00
% 2.29/1.28  Cooper               : 0.00
% 2.29/1.28  Total                : 0.53
% 2.29/1.28  Index Insertion      : 0.00
% 2.29/1.28  Index Deletion       : 0.00
% 2.29/1.28  Index Matching       : 0.00
% 2.29/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
