%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:05 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 240 expanded)
%              Number of leaves         :   42 ( 110 expanded)
%              Depth                    :   18
%              Number of atoms          :  174 ( 746 expanded)
%              Number of equality atoms :   15 ( 114 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k3_mcart_1 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(f_159,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_141,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_105,axiom,(
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

tff(f_125,axiom,(
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

tff(f_83,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_54,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_52,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_50,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_48,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_46,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_44,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_63,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(A_71,k3_tarski(B_72))
      | ~ r2_hidden(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_67,plain,(
    ! [A_73] :
      ( r1_tarski(A_73,k1_xboole_0)
      | ~ r2_hidden(A_73,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_63])).

tff(c_72,plain,
    ( r1_tarski('#skF_1'(k4_orders_2('#skF_5','#skF_6')),k1_xboole_0)
    | k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_67])).

tff(c_73,plain,(
    k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_104,plain,(
    ! [A_89,B_90] :
      ( ~ v1_xboole_0(k4_orders_2(A_89,B_90))
      | ~ m1_orders_1(B_90,k1_orders_1(u1_struct_0(A_89)))
      | ~ l1_orders_2(A_89)
      | ~ v5_orders_2(A_89)
      | ~ v4_orders_2(A_89)
      | ~ v3_orders_2(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_107,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_104])).

tff(c_110,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2,c_73,c_107])).

tff(c_112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_110])).

tff(c_114,plain,(
    k4_orders_2('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_113,plain,(
    r1_tarski('#skF_1'(k4_orders_2('#skF_5','#skF_6')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_118,plain,(
    '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_113,c_4])).

tff(c_123,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6'))
    | k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_8])).

tff(c_126,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_123])).

tff(c_179,plain,(
    ! [D_114,A_115,B_116] :
      ( m2_orders_2(D_114,A_115,B_116)
      | ~ r2_hidden(D_114,k4_orders_2(A_115,B_116))
      | ~ m1_orders_1(B_116,k1_orders_1(u1_struct_0(A_115)))
      | ~ l1_orders_2(A_115)
      | ~ v5_orders_2(A_115)
      | ~ v4_orders_2(A_115)
      | ~ v3_orders_2(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_181,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_126,c_179])).

tff(c_187,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_181])).

tff(c_188,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_187])).

tff(c_40,plain,(
    ! [C_65,A_62,B_63] :
      ( v6_orders_2(C_65,A_62)
      | ~ m2_orders_2(C_65,A_62,B_63)
      | ~ m1_orders_1(B_63,k1_orders_1(u1_struct_0(A_62)))
      | ~ l1_orders_2(A_62)
      | ~ v5_orders_2(A_62)
      | ~ v4_orders_2(A_62)
      | ~ v3_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_191,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_5')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_188,c_40])).

tff(c_194,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_191])).

tff(c_195,plain,(
    v6_orders_2(k1_xboole_0,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_194])).

tff(c_196,plain,(
    ! [C_117,A_118,B_119] :
      ( m1_subset_1(C_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ m2_orders_2(C_117,A_118,B_119)
      | ~ m1_orders_1(B_119,k1_orders_1(u1_struct_0(A_118)))
      | ~ l1_orders_2(A_118)
      | ~ v5_orders_2(A_118)
      | ~ v4_orders_2(A_118)
      | ~ v3_orders_2(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_198,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_188,c_196])).

tff(c_201,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_198])).

tff(c_202,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_201])).

tff(c_238,plain,(
    ! [A_128,B_129] :
      ( ~ m2_orders_2(k1_xboole_0,A_128,B_129)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ v6_orders_2(k1_xboole_0,A_128)
      | ~ m1_orders_1(B_129,k1_orders_1(u1_struct_0(A_128)))
      | ~ l1_orders_2(A_128)
      | ~ v5_orders_2(A_128)
      | ~ v4_orders_2(A_128)
      | ~ v3_orders_2(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_240,plain,(
    ! [B_129] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_129)
      | ~ v6_orders_2(k1_xboole_0,'#skF_5')
      | ~ m1_orders_1(B_129,k1_orders_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_202,c_238])).

tff(c_243,plain,(
    ! [B_129] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_129)
      | ~ m1_orders_1(B_129,k1_orders_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_195,c_240])).

tff(c_246,plain,(
    ! [B_133] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_133)
      | ~ m1_orders_1(B_133,k1_orders_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_243])).

tff(c_249,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_246])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:14:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.34  
% 2.47/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.34  %$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k3_mcart_1 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.47/1.34  
% 2.47/1.34  %Foreground sorts:
% 2.47/1.34  
% 2.47/1.34  
% 2.47/1.34  %Background operators:
% 2.47/1.34  
% 2.47/1.34  
% 2.47/1.34  %Foreground operators:
% 2.47/1.34  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.47/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.47/1.34  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.47/1.34  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.47/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.34  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.47/1.34  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.47/1.34  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.47/1.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.47/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.34  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.47/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.47/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.47/1.34  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.47/1.34  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.47/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.34  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.47/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.47/1.34  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.47/1.34  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.47/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.34  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.47/1.34  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.47/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.47/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.34  
% 2.47/1.35  tff(f_159, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.47/1.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.47/1.35  tff(f_50, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 2.47/1.35  tff(f_34, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.47/1.35  tff(f_141, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.47/1.35  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.47/1.35  tff(f_105, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.47/1.35  tff(f_125, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.47/1.35  tff(f_83, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_orders_2)).
% 2.47/1.35  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.47/1.35  tff(c_54, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.47/1.35  tff(c_52, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.47/1.35  tff(c_50, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.47/1.35  tff(c_48, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.47/1.35  tff(c_46, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.47/1.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.47/1.35  tff(c_8, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.47/1.35  tff(c_44, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.47/1.35  tff(c_63, plain, (![A_71, B_72]: (r1_tarski(A_71, k3_tarski(B_72)) | ~r2_hidden(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.47/1.35  tff(c_67, plain, (![A_73]: (r1_tarski(A_73, k1_xboole_0) | ~r2_hidden(A_73, k4_orders_2('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_63])).
% 2.47/1.35  tff(c_72, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_5', '#skF_6')), k1_xboole_0) | k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_67])).
% 2.47/1.35  tff(c_73, plain, (k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_72])).
% 2.47/1.35  tff(c_104, plain, (![A_89, B_90]: (~v1_xboole_0(k4_orders_2(A_89, B_90)) | ~m1_orders_1(B_90, k1_orders_1(u1_struct_0(A_89))) | ~l1_orders_2(A_89) | ~v5_orders_2(A_89) | ~v4_orders_2(A_89) | ~v3_orders_2(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.47/1.35  tff(c_107, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_104])).
% 2.47/1.35  tff(c_110, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_2, c_73, c_107])).
% 2.47/1.35  tff(c_112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_110])).
% 2.47/1.35  tff(c_114, plain, (k4_orders_2('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_72])).
% 2.47/1.35  tff(c_113, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_5', '#skF_6')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_72])).
% 2.47/1.35  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.47/1.35  tff(c_118, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_113, c_4])).
% 2.47/1.35  tff(c_123, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6')) | k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_118, c_8])).
% 2.47/1.35  tff(c_126, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_114, c_123])).
% 2.47/1.35  tff(c_179, plain, (![D_114, A_115, B_116]: (m2_orders_2(D_114, A_115, B_116) | ~r2_hidden(D_114, k4_orders_2(A_115, B_116)) | ~m1_orders_1(B_116, k1_orders_1(u1_struct_0(A_115))) | ~l1_orders_2(A_115) | ~v5_orders_2(A_115) | ~v4_orders_2(A_115) | ~v3_orders_2(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.47/1.35  tff(c_181, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_126, c_179])).
% 2.47/1.35  tff(c_187, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_181])).
% 2.47/1.35  tff(c_188, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_187])).
% 2.47/1.35  tff(c_40, plain, (![C_65, A_62, B_63]: (v6_orders_2(C_65, A_62) | ~m2_orders_2(C_65, A_62, B_63) | ~m1_orders_1(B_63, k1_orders_1(u1_struct_0(A_62))) | ~l1_orders_2(A_62) | ~v5_orders_2(A_62) | ~v4_orders_2(A_62) | ~v3_orders_2(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.47/1.35  tff(c_191, plain, (v6_orders_2(k1_xboole_0, '#skF_5') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_188, c_40])).
% 2.47/1.35  tff(c_194, plain, (v6_orders_2(k1_xboole_0, '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_191])).
% 2.47/1.35  tff(c_195, plain, (v6_orders_2(k1_xboole_0, '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_194])).
% 2.47/1.35  tff(c_196, plain, (![C_117, A_118, B_119]: (m1_subset_1(C_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~m2_orders_2(C_117, A_118, B_119) | ~m1_orders_1(B_119, k1_orders_1(u1_struct_0(A_118))) | ~l1_orders_2(A_118) | ~v5_orders_2(A_118) | ~v4_orders_2(A_118) | ~v3_orders_2(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.47/1.35  tff(c_198, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_188, c_196])).
% 2.47/1.35  tff(c_201, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_198])).
% 2.47/1.35  tff(c_202, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_201])).
% 2.47/1.35  tff(c_238, plain, (![A_128, B_129]: (~m2_orders_2(k1_xboole_0, A_128, B_129) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_128))) | ~v6_orders_2(k1_xboole_0, A_128) | ~m1_orders_1(B_129, k1_orders_1(u1_struct_0(A_128))) | ~l1_orders_2(A_128) | ~v5_orders_2(A_128) | ~v4_orders_2(A_128) | ~v3_orders_2(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.47/1.35  tff(c_240, plain, (![B_129]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_129) | ~v6_orders_2(k1_xboole_0, '#skF_5') | ~m1_orders_1(B_129, k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_202, c_238])).
% 2.47/1.35  tff(c_243, plain, (![B_129]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_129) | ~m1_orders_1(B_129, k1_orders_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_195, c_240])).
% 2.47/1.35  tff(c_246, plain, (![B_133]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_133) | ~m1_orders_1(B_133, k1_orders_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_243])).
% 2.47/1.35  tff(c_249, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_246])).
% 2.47/1.35  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_249])).
% 2.47/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.35  
% 2.47/1.35  Inference rules
% 2.47/1.35  ----------------------
% 2.47/1.35  #Ref     : 0
% 2.47/1.35  #Sup     : 38
% 2.47/1.35  #Fact    : 0
% 2.47/1.35  #Define  : 0
% 2.47/1.35  #Split   : 1
% 2.47/1.35  #Chain   : 0
% 2.47/1.35  #Close   : 0
% 2.47/1.35  
% 2.47/1.35  Ordering : KBO
% 2.47/1.35  
% 2.47/1.35  Simplification rules
% 2.47/1.35  ----------------------
% 2.47/1.35  #Subsume      : 3
% 2.47/1.35  #Demod        : 51
% 2.47/1.35  #Tautology    : 13
% 2.47/1.35  #SimpNegUnit  : 15
% 2.47/1.35  #BackRed      : 3
% 2.47/1.35  
% 2.47/1.35  #Partial instantiations: 0
% 2.47/1.35  #Strategies tried      : 1
% 2.47/1.36  
% 2.47/1.36  Timing (in seconds)
% 2.47/1.36  ----------------------
% 2.47/1.36  Preprocessing        : 0.35
% 2.47/1.36  Parsing              : 0.19
% 2.47/1.36  CNF conversion       : 0.03
% 2.47/1.36  Main loop            : 0.21
% 2.47/1.36  Inferencing          : 0.07
% 2.47/1.36  Reduction            : 0.06
% 2.47/1.36  Demodulation         : 0.04
% 2.47/1.36  BG Simplification    : 0.02
% 2.47/1.36  Subsumption          : 0.04
% 2.47/1.36  Abstraction          : 0.01
% 2.47/1.36  MUC search           : 0.00
% 2.47/1.36  Cooper               : 0.00
% 2.47/1.36  Total                : 0.59
% 2.47/1.36  Index Insertion      : 0.00
% 2.47/1.36  Index Deletion       : 0.00
% 2.47/1.36  Index Matching       : 0.00
% 2.47/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
