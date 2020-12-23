%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:02 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 249 expanded)
%              Number of leaves         :   43 ( 113 expanded)
%              Depth                    :   18
%              Number of atoms          :  180 ( 764 expanded)
%              Number of equality atoms :   16 ( 117 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k4_tarski > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_163,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_145,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_109,axiom,(
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

tff(f_129,axiom,(
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

tff(f_87,axiom,(
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

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_60,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_58,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_56,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_54,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_52,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_14,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_1'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_50,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_71,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,k3_tarski(B_71))
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_101,plain,(
    ! [A_75] :
      ( r1_tarski(A_75,k1_xboole_0)
      | ~ r2_hidden(A_75,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_71])).

tff(c_106,plain,
    ( r1_tarski('#skF_1'(k4_orders_2('#skF_5','#skF_6')),k1_xboole_0)
    | k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_101])).

tff(c_117,plain,(
    k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_155,plain,(
    ! [A_89,B_90] :
      ( ~ v1_xboole_0(k4_orders_2(A_89,B_90))
      | ~ m1_orders_1(B_90,k1_orders_1(u1_struct_0(A_89)))
      | ~ l1_orders_2(A_89)
      | ~ v5_orders_2(A_89)
      | ~ v4_orders_2(A_89)
      | ~ v3_orders_2(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_158,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_155])).

tff(c_161,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_2,c_117,c_158])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_161])).

tff(c_165,plain,(
    k4_orders_2('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_164,plain,(
    r1_tarski('#skF_1'(k4_orders_2('#skF_5','#skF_6')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_75,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(B_72,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_75])).

tff(c_171,plain,(
    '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_164,c_83])).

tff(c_186,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6'))
    | k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_14])).

tff(c_193,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_186])).

tff(c_256,plain,(
    ! [D_103,A_104,B_105] :
      ( m2_orders_2(D_103,A_104,B_105)
      | ~ r2_hidden(D_103,k4_orders_2(A_104,B_105))
      | ~ m1_orders_1(B_105,k1_orders_1(u1_struct_0(A_104)))
      | ~ l1_orders_2(A_104)
      | ~ v5_orders_2(A_104)
      | ~ v4_orders_2(A_104)
      | ~ v3_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_258,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_193,c_256])).

tff(c_264,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_258])).

tff(c_265,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_264])).

tff(c_46,plain,(
    ! [C_63,A_60,B_61] :
      ( v6_orders_2(C_63,A_60)
      | ~ m2_orders_2(C_63,A_60,B_61)
      | ~ m1_orders_1(B_61,k1_orders_1(u1_struct_0(A_60)))
      | ~ l1_orders_2(A_60)
      | ~ v5_orders_2(A_60)
      | ~ v4_orders_2(A_60)
      | ~ v3_orders_2(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_268,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_5')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_265,c_46])).

tff(c_271,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_268])).

tff(c_272,plain,(
    v6_orders_2(k1_xboole_0,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_271])).

tff(c_273,plain,(
    ! [C_106,A_107,B_108] :
      ( m1_subset_1(C_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m2_orders_2(C_106,A_107,B_108)
      | ~ m1_orders_1(B_108,k1_orders_1(u1_struct_0(A_107)))
      | ~ l1_orders_2(A_107)
      | ~ v5_orders_2(A_107)
      | ~ v4_orders_2(A_107)
      | ~ v3_orders_2(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_275,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_265,c_273])).

tff(c_278,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_275])).

tff(c_279,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_278])).

tff(c_287,plain,(
    ! [A_112,B_113] :
      ( ~ m2_orders_2(k1_xboole_0,A_112,B_113)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ v6_orders_2(k1_xboole_0,A_112)
      | ~ m1_orders_1(B_113,k1_orders_1(u1_struct_0(A_112)))
      | ~ l1_orders_2(A_112)
      | ~ v5_orders_2(A_112)
      | ~ v4_orders_2(A_112)
      | ~ v3_orders_2(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_289,plain,(
    ! [B_113] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_113)
      | ~ v6_orders_2(k1_xboole_0,'#skF_5')
      | ~ m1_orders_1(B_113,k1_orders_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_279,c_287])).

tff(c_292,plain,(
    ! [B_113] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_113)
      | ~ m1_orders_1(B_113,k1_orders_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_272,c_289])).

tff(c_336,plain,(
    ! [B_117] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_117)
      | ~ m1_orders_1(B_117,k1_orders_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_292])).

tff(c_339,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_336])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:55:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.35  
% 2.50/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.36  %$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k4_tarski > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.50/1.36  
% 2.50/1.36  %Foreground sorts:
% 2.50/1.36  
% 2.50/1.36  
% 2.50/1.36  %Background operators:
% 2.50/1.36  
% 2.50/1.36  
% 2.50/1.36  %Foreground operators:
% 2.50/1.36  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.50/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.50/1.36  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.50/1.36  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.50/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.50/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.50/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.36  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.50/1.36  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.50/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.50/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.36  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.50/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.50/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.50/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.50/1.36  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.50/1.36  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.50/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.36  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.50/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.50/1.36  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.50/1.36  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.50/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.50/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.50/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.36  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.50/1.36  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.50/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.36  
% 2.73/1.37  tff(f_163, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.73/1.37  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.73/1.37  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.73/1.37  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.73/1.37  tff(f_145, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.73/1.37  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.73/1.37  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.73/1.37  tff(f_109, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.73/1.37  tff(f_129, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.73/1.37  tff(f_87, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_orders_2)).
% 2.73/1.37  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.73/1.37  tff(c_60, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.73/1.37  tff(c_58, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.73/1.37  tff(c_56, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.73/1.37  tff(c_54, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.73/1.37  tff(c_52, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.73/1.37  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.73/1.37  tff(c_14, plain, (![A_6]: (r2_hidden('#skF_1'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.73/1.37  tff(c_50, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.73/1.37  tff(c_71, plain, (![A_70, B_71]: (r1_tarski(A_70, k3_tarski(B_71)) | ~r2_hidden(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.73/1.37  tff(c_101, plain, (![A_75]: (r1_tarski(A_75, k1_xboole_0) | ~r2_hidden(A_75, k4_orders_2('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_71])).
% 2.73/1.37  tff(c_106, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_5', '#skF_6')), k1_xboole_0) | k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_101])).
% 2.73/1.37  tff(c_117, plain, (k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_106])).
% 2.73/1.37  tff(c_155, plain, (![A_89, B_90]: (~v1_xboole_0(k4_orders_2(A_89, B_90)) | ~m1_orders_1(B_90, k1_orders_1(u1_struct_0(A_89))) | ~l1_orders_2(A_89) | ~v5_orders_2(A_89) | ~v4_orders_2(A_89) | ~v3_orders_2(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.73/1.37  tff(c_158, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_155])).
% 2.73/1.37  tff(c_161, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_2, c_117, c_158])).
% 2.73/1.37  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_161])).
% 2.73/1.37  tff(c_165, plain, (k4_orders_2('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_106])).
% 2.73/1.37  tff(c_164, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_5', '#skF_6')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_106])).
% 2.73/1.37  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.73/1.37  tff(c_75, plain, (![B_72, A_73]: (B_72=A_73 | ~r1_tarski(B_72, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.73/1.37  tff(c_83, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_75])).
% 2.73/1.37  tff(c_171, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_164, c_83])).
% 2.73/1.37  tff(c_186, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6')) | k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_171, c_14])).
% 2.73/1.37  tff(c_193, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_165, c_186])).
% 2.73/1.37  tff(c_256, plain, (![D_103, A_104, B_105]: (m2_orders_2(D_103, A_104, B_105) | ~r2_hidden(D_103, k4_orders_2(A_104, B_105)) | ~m1_orders_1(B_105, k1_orders_1(u1_struct_0(A_104))) | ~l1_orders_2(A_104) | ~v5_orders_2(A_104) | ~v4_orders_2(A_104) | ~v3_orders_2(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.73/1.37  tff(c_258, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_193, c_256])).
% 2.73/1.37  tff(c_264, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_258])).
% 2.73/1.37  tff(c_265, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_62, c_264])).
% 2.73/1.37  tff(c_46, plain, (![C_63, A_60, B_61]: (v6_orders_2(C_63, A_60) | ~m2_orders_2(C_63, A_60, B_61) | ~m1_orders_1(B_61, k1_orders_1(u1_struct_0(A_60))) | ~l1_orders_2(A_60) | ~v5_orders_2(A_60) | ~v4_orders_2(A_60) | ~v3_orders_2(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.73/1.37  tff(c_268, plain, (v6_orders_2(k1_xboole_0, '#skF_5') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_265, c_46])).
% 2.73/1.37  tff(c_271, plain, (v6_orders_2(k1_xboole_0, '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_268])).
% 2.73/1.37  tff(c_272, plain, (v6_orders_2(k1_xboole_0, '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_271])).
% 2.73/1.37  tff(c_273, plain, (![C_106, A_107, B_108]: (m1_subset_1(C_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~m2_orders_2(C_106, A_107, B_108) | ~m1_orders_1(B_108, k1_orders_1(u1_struct_0(A_107))) | ~l1_orders_2(A_107) | ~v5_orders_2(A_107) | ~v4_orders_2(A_107) | ~v3_orders_2(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.73/1.37  tff(c_275, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_265, c_273])).
% 2.73/1.37  tff(c_278, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_275])).
% 2.73/1.37  tff(c_279, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_278])).
% 2.73/1.37  tff(c_287, plain, (![A_112, B_113]: (~m2_orders_2(k1_xboole_0, A_112, B_113) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_112))) | ~v6_orders_2(k1_xboole_0, A_112) | ~m1_orders_1(B_113, k1_orders_1(u1_struct_0(A_112))) | ~l1_orders_2(A_112) | ~v5_orders_2(A_112) | ~v4_orders_2(A_112) | ~v3_orders_2(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.73/1.37  tff(c_289, plain, (![B_113]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_113) | ~v6_orders_2(k1_xboole_0, '#skF_5') | ~m1_orders_1(B_113, k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_279, c_287])).
% 2.73/1.37  tff(c_292, plain, (![B_113]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_113) | ~m1_orders_1(B_113, k1_orders_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_272, c_289])).
% 2.73/1.37  tff(c_336, plain, (![B_117]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_117) | ~m1_orders_1(B_117, k1_orders_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_292])).
% 2.73/1.37  tff(c_339, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_336])).
% 2.73/1.37  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_265, c_339])).
% 2.73/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.37  
% 2.73/1.37  Inference rules
% 2.73/1.37  ----------------------
% 2.73/1.37  #Ref     : 0
% 2.73/1.37  #Sup     : 53
% 2.73/1.37  #Fact    : 0
% 2.73/1.37  #Define  : 0
% 2.73/1.37  #Split   : 1
% 2.73/1.37  #Chain   : 0
% 2.73/1.38  #Close   : 0
% 2.73/1.38  
% 2.73/1.38  Ordering : KBO
% 2.73/1.38  
% 2.73/1.38  Simplification rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Subsume      : 4
% 2.73/1.38  #Demod        : 64
% 2.73/1.38  #Tautology    : 23
% 2.73/1.38  #SimpNegUnit  : 16
% 2.73/1.38  #BackRed      : 3
% 2.73/1.38  
% 2.73/1.38  #Partial instantiations: 0
% 2.73/1.38  #Strategies tried      : 1
% 2.73/1.38  
% 2.73/1.38  Timing (in seconds)
% 2.73/1.38  ----------------------
% 2.73/1.38  Preprocessing        : 0.35
% 2.73/1.38  Parsing              : 0.18
% 2.73/1.38  CNF conversion       : 0.03
% 2.73/1.38  Main loop            : 0.24
% 2.73/1.38  Inferencing          : 0.08
% 2.73/1.38  Reduction            : 0.08
% 2.73/1.38  Demodulation         : 0.06
% 2.73/1.38  BG Simplification    : 0.02
% 2.73/1.38  Subsumption          : 0.05
% 2.73/1.38  Abstraction          : 0.01
% 2.73/1.38  MUC search           : 0.00
% 2.73/1.38  Cooper               : 0.00
% 2.73/1.38  Total                : 0.64
% 2.73/1.38  Index Insertion      : 0.00
% 2.73/1.38  Index Deletion       : 0.00
% 2.73/1.38  Index Matching       : 0.00
% 2.73/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
