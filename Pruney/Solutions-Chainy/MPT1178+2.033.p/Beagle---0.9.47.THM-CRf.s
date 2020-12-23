%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:06 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 231 expanded)
%              Number of leaves         :   41 ( 107 expanded)
%              Depth                    :   17
%              Number of atoms          :  175 ( 773 expanded)
%              Number of equality atoms :   23 ( 178 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k4_tarski > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(f_171,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_153,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_97,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_117,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_75,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_orders_2)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_56,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_54,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_52,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_50,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_48,plain,(
    m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_46,plain,(
    k3_tarski(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,(
    ! [A_69,B_70] :
      ( k3_tarski(A_69) != k1_xboole_0
      | ~ r2_hidden(B_70,A_69)
      | k1_xboole_0 = B_70 ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_91,plain,(
    ! [A_71] :
      ( k3_tarski(A_71) != k1_xboole_0
      | '#skF_1'(A_71) = k1_xboole_0
      | k1_xboole_0 = A_71 ) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_99,plain,
    ( '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0
    | k4_orders_2('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_91])).

tff(c_101,plain,(
    k4_orders_2('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_142,plain,(
    ! [A_87,B_88] :
      ( ~ v1_xboole_0(k4_orders_2(A_87,B_88))
      | ~ m1_orders_1(B_88,k1_orders_1(u1_struct_0(A_87)))
      | ~ l1_orders_2(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v4_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_145,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_142])).

tff(c_148,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2,c_101,c_145])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_148])).

tff(c_152,plain,(
    k4_orders_2('#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_151,plain,(
    '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_163,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7'))
    | k4_orders_2('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_4])).

tff(c_166,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_163])).

tff(c_244,plain,(
    ! [D_119,A_120,B_121] :
      ( m2_orders_2(D_119,A_120,B_121)
      | ~ r2_hidden(D_119,k4_orders_2(A_120,B_121))
      | ~ m1_orders_1(B_121,k1_orders_1(u1_struct_0(A_120)))
      | ~ l1_orders_2(A_120)
      | ~ v5_orders_2(A_120)
      | ~ v4_orders_2(A_120)
      | ~ v3_orders_2(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_248,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_166,c_244])).

tff(c_261,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_248])).

tff(c_262,plain,(
    m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_261])).

tff(c_36,plain,(
    ! [C_58,A_55,B_56] :
      ( v6_orders_2(C_58,A_55)
      | ~ m2_orders_2(C_58,A_55,B_56)
      | ~ m1_orders_1(B_56,k1_orders_1(u1_struct_0(A_55)))
      | ~ l1_orders_2(A_55)
      | ~ v5_orders_2(A_55)
      | ~ v4_orders_2(A_55)
      | ~ v3_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_269,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_6')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_262,c_36])).

tff(c_274,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_269])).

tff(c_275,plain,(
    v6_orders_2(k1_xboole_0,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_274])).

tff(c_276,plain,(
    ! [C_122,A_123,B_124] :
      ( m1_subset_1(C_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m2_orders_2(C_122,A_123,B_124)
      | ~ m1_orders_1(B_124,k1_orders_1(u1_struct_0(A_123)))
      | ~ l1_orders_2(A_123)
      | ~ v5_orders_2(A_123)
      | ~ v4_orders_2(A_123)
      | ~ v3_orders_2(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_278,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_262,c_276])).

tff(c_281,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_278])).

tff(c_282,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_281])).

tff(c_304,plain,(
    ! [A_127,B_128] :
      ( ~ m2_orders_2(k1_xboole_0,A_127,B_128)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ v6_orders_2(k1_xboole_0,A_127)
      | ~ m1_orders_1(B_128,k1_orders_1(u1_struct_0(A_127)))
      | ~ l1_orders_2(A_127)
      | ~ v5_orders_2(A_127)
      | ~ v4_orders_2(A_127)
      | ~ v3_orders_2(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_306,plain,(
    ! [B_128] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_128)
      | ~ v6_orders_2(k1_xboole_0,'#skF_6')
      | ~ m1_orders_1(B_128,k1_orders_1(u1_struct_0('#skF_6')))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_282,c_304])).

tff(c_309,plain,(
    ! [B_128] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_128)
      | ~ m1_orders_1(B_128,k1_orders_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_275,c_306])).

tff(c_311,plain,(
    ! [B_129] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_129)
      | ~ m1_orders_1(B_129,k1_orders_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_309])).

tff(c_314,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_311])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.34  
% 2.54/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.35  %$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k4_tarski > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3
% 2.54/1.35  
% 2.54/1.35  %Foreground sorts:
% 2.54/1.35  
% 2.54/1.35  
% 2.54/1.35  %Background operators:
% 2.54/1.35  
% 2.54/1.35  
% 2.54/1.35  %Foreground operators:
% 2.54/1.35  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.54/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.54/1.35  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.54/1.35  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.54/1.35  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.54/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.54/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.35  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.54/1.35  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.54/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.54/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.54/1.35  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.54/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.54/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.54/1.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.54/1.35  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.54/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.35  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.54/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.54/1.35  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.54/1.35  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.54/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.35  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.54/1.35  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.54/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.54/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.54/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.35  
% 2.54/1.36  tff(f_171, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.54/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.54/1.36  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.54/1.36  tff(f_153, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 2.54/1.36  tff(f_133, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.54/1.36  tff(f_97, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.54/1.36  tff(f_117, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.54/1.36  tff(f_75, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_orders_2)).
% 2.54/1.36  tff(c_58, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 2.54/1.36  tff(c_56, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 2.54/1.36  tff(c_54, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 2.54/1.36  tff(c_52, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 2.54/1.36  tff(c_50, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 2.54/1.36  tff(c_48, plain, (m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 2.54/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.54/1.36  tff(c_46, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_171])).
% 2.54/1.36  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.54/1.36  tff(c_82, plain, (![A_69, B_70]: (k3_tarski(A_69)!=k1_xboole_0 | ~r2_hidden(B_70, A_69) | k1_xboole_0=B_70)), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.54/1.36  tff(c_91, plain, (![A_71]: (k3_tarski(A_71)!=k1_xboole_0 | '#skF_1'(A_71)=k1_xboole_0 | k1_xboole_0=A_71)), inference(resolution, [status(thm)], [c_4, c_82])).
% 2.54/1.36  tff(c_99, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0 | k4_orders_2('#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_46, c_91])).
% 2.54/1.36  tff(c_101, plain, (k4_orders_2('#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_99])).
% 2.54/1.36  tff(c_142, plain, (![A_87, B_88]: (~v1_xboole_0(k4_orders_2(A_87, B_88)) | ~m1_orders_1(B_88, k1_orders_1(u1_struct_0(A_87))) | ~l1_orders_2(A_87) | ~v5_orders_2(A_87) | ~v4_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.54/1.36  tff(c_145, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_48, c_142])).
% 2.54/1.36  tff(c_148, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2, c_101, c_145])).
% 2.54/1.36  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_148])).
% 2.54/1.36  tff(c_152, plain, (k4_orders_2('#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_99])).
% 2.54/1.36  tff(c_151, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_99])).
% 2.54/1.36  tff(c_163, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7')) | k4_orders_2('#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_151, c_4])).
% 2.54/1.36  tff(c_166, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_152, c_163])).
% 2.54/1.36  tff(c_244, plain, (![D_119, A_120, B_121]: (m2_orders_2(D_119, A_120, B_121) | ~r2_hidden(D_119, k4_orders_2(A_120, B_121)) | ~m1_orders_1(B_121, k1_orders_1(u1_struct_0(A_120))) | ~l1_orders_2(A_120) | ~v5_orders_2(A_120) | ~v4_orders_2(A_120) | ~v3_orders_2(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.54/1.36  tff(c_248, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_166, c_244])).
% 2.54/1.36  tff(c_261, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_248])).
% 2.54/1.36  tff(c_262, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_58, c_261])).
% 2.54/1.36  tff(c_36, plain, (![C_58, A_55, B_56]: (v6_orders_2(C_58, A_55) | ~m2_orders_2(C_58, A_55, B_56) | ~m1_orders_1(B_56, k1_orders_1(u1_struct_0(A_55))) | ~l1_orders_2(A_55) | ~v5_orders_2(A_55) | ~v4_orders_2(A_55) | ~v3_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.54/1.36  tff(c_269, plain, (v6_orders_2(k1_xboole_0, '#skF_6') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_262, c_36])).
% 2.54/1.36  tff(c_274, plain, (v6_orders_2(k1_xboole_0, '#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_269])).
% 2.54/1.36  tff(c_275, plain, (v6_orders_2(k1_xboole_0, '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_58, c_274])).
% 2.54/1.36  tff(c_276, plain, (![C_122, A_123, B_124]: (m1_subset_1(C_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~m2_orders_2(C_122, A_123, B_124) | ~m1_orders_1(B_124, k1_orders_1(u1_struct_0(A_123))) | ~l1_orders_2(A_123) | ~v5_orders_2(A_123) | ~v4_orders_2(A_123) | ~v3_orders_2(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.54/1.36  tff(c_278, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_262, c_276])).
% 2.54/1.36  tff(c_281, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_278])).
% 2.54/1.36  tff(c_282, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_58, c_281])).
% 2.54/1.36  tff(c_304, plain, (![A_127, B_128]: (~m2_orders_2(k1_xboole_0, A_127, B_128) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_127))) | ~v6_orders_2(k1_xboole_0, A_127) | ~m1_orders_1(B_128, k1_orders_1(u1_struct_0(A_127))) | ~l1_orders_2(A_127) | ~v5_orders_2(A_127) | ~v4_orders_2(A_127) | ~v3_orders_2(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.54/1.36  tff(c_306, plain, (![B_128]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_128) | ~v6_orders_2(k1_xboole_0, '#skF_6') | ~m1_orders_1(B_128, k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_282, c_304])).
% 2.54/1.36  tff(c_309, plain, (![B_128]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_128) | ~m1_orders_1(B_128, k1_orders_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_275, c_306])).
% 2.54/1.36  tff(c_311, plain, (![B_129]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_129) | ~m1_orders_1(B_129, k1_orders_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_309])).
% 2.54/1.36  tff(c_314, plain, (~m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_48, c_311])).
% 2.54/1.36  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_262, c_314])).
% 2.54/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.36  
% 2.54/1.36  Inference rules
% 2.54/1.36  ----------------------
% 2.54/1.36  #Ref     : 0
% 2.54/1.36  #Sup     : 52
% 2.54/1.36  #Fact    : 0
% 2.54/1.36  #Define  : 0
% 2.54/1.36  #Split   : 1
% 2.54/1.36  #Chain   : 0
% 2.54/1.36  #Close   : 0
% 2.54/1.36  
% 2.54/1.36  Ordering : KBO
% 2.54/1.36  
% 2.54/1.36  Simplification rules
% 2.54/1.36  ----------------------
% 2.54/1.36  #Subsume      : 2
% 2.54/1.36  #Demod        : 61
% 2.54/1.36  #Tautology    : 21
% 2.54/1.36  #SimpNegUnit  : 17
% 2.54/1.36  #BackRed      : 1
% 2.54/1.36  
% 2.54/1.36  #Partial instantiations: 0
% 2.54/1.36  #Strategies tried      : 1
% 2.54/1.36  
% 2.54/1.36  Timing (in seconds)
% 2.54/1.36  ----------------------
% 2.68/1.37  Preprocessing        : 0.36
% 2.68/1.37  Parsing              : 0.19
% 2.68/1.37  CNF conversion       : 0.03
% 2.68/1.37  Main loop            : 0.24
% 2.68/1.37  Inferencing          : 0.09
% 2.68/1.37  Reduction            : 0.07
% 2.68/1.37  Demodulation         : 0.05
% 2.68/1.37  BG Simplification    : 0.02
% 2.68/1.37  Subsumption          : 0.04
% 2.68/1.37  Abstraction          : 0.01
% 2.68/1.37  MUC search           : 0.00
% 2.68/1.37  Cooper               : 0.00
% 2.68/1.37  Total                : 0.64
% 2.68/1.37  Index Insertion      : 0.00
% 2.68/1.37  Index Deletion       : 0.00
% 2.68/1.37  Index Matching       : 0.00
% 2.68/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
