%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:06 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 231 expanded)
%              Number of leaves         :   41 ( 107 expanded)
%              Depth                    :   17
%              Number of atoms          :  175 ( 773 expanded)
%              Number of equality atoms :   23 ( 178 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_mcart_1 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

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
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

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
    ! [A_77,B_78] :
      ( k3_tarski(A_77) != k1_xboole_0
      | ~ r2_hidden(B_78,A_77)
      | k1_xboole_0 = B_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_91,plain,(
    ! [A_79] :
      ( k3_tarski(A_79) != k1_xboole_0
      | '#skF_1'(A_79) = k1_xboole_0
      | k1_xboole_0 = A_79 ) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_99,plain,
    ( '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0
    | k4_orders_2('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_91])).

tff(c_101,plain,(
    k4_orders_2('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_142,plain,(
    ! [A_107,B_108] :
      ( ~ v1_xboole_0(k4_orders_2(A_107,B_108))
      | ~ m1_orders_1(B_108,k1_orders_1(u1_struct_0(A_107)))
      | ~ l1_orders_2(A_107)
      | ~ v5_orders_2(A_107)
      | ~ v4_orders_2(A_107)
      | ~ v3_orders_2(A_107)
      | v2_struct_0(A_107) ) ),
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
    ! [D_159,A_160,B_161] :
      ( m2_orders_2(D_159,A_160,B_161)
      | ~ r2_hidden(D_159,k4_orders_2(A_160,B_161))
      | ~ m1_orders_1(B_161,k1_orders_1(u1_struct_0(A_160)))
      | ~ l1_orders_2(A_160)
      | ~ v5_orders_2(A_160)
      | ~ v4_orders_2(A_160)
      | ~ v3_orders_2(A_160)
      | v2_struct_0(A_160) ) ),
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
    ! [C_66,A_63,B_64] :
      ( v6_orders_2(C_66,A_63)
      | ~ m2_orders_2(C_66,A_63,B_64)
      | ~ m1_orders_1(B_64,k1_orders_1(u1_struct_0(A_63)))
      | ~ l1_orders_2(A_63)
      | ~ v5_orders_2(A_63)
      | ~ v4_orders_2(A_63)
      | ~ v3_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
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
    ! [C_162,A_163,B_164] :
      ( m1_subset_1(C_162,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ m2_orders_2(C_162,A_163,B_164)
      | ~ m1_orders_1(B_164,k1_orders_1(u1_struct_0(A_163)))
      | ~ l1_orders_2(A_163)
      | ~ v5_orders_2(A_163)
      | ~ v4_orders_2(A_163)
      | ~ v3_orders_2(A_163)
      | v2_struct_0(A_163) ) ),
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
    ! [A_167,B_168] :
      ( ~ m2_orders_2(k1_xboole_0,A_167,B_168)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ v6_orders_2(k1_xboole_0,A_167)
      | ~ m1_orders_1(B_168,k1_orders_1(u1_struct_0(A_167)))
      | ~ l1_orders_2(A_167)
      | ~ v5_orders_2(A_167)
      | ~ v4_orders_2(A_167)
      | ~ v3_orders_2(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_306,plain,(
    ! [B_168] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_168)
      | ~ v6_orders_2(k1_xboole_0,'#skF_6')
      | ~ m1_orders_1(B_168,k1_orders_1(u1_struct_0('#skF_6')))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_282,c_304])).

tff(c_309,plain,(
    ! [B_168] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_168)
      | ~ m1_orders_1(B_168,k1_orders_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_275,c_306])).

tff(c_311,plain,(
    ! [B_169] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_169)
      | ~ m1_orders_1(B_169,k1_orders_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_309])).

tff(c_314,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_311])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:17:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.32  
% 2.18/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.32  %$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_mcart_1 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3
% 2.18/1.32  
% 2.18/1.32  %Foreground sorts:
% 2.18/1.32  
% 2.18/1.32  
% 2.18/1.32  %Background operators:
% 2.18/1.32  
% 2.18/1.32  
% 2.18/1.32  %Foreground operators:
% 2.18/1.32  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.18/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.18/1.32  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.18/1.32  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.18/1.32  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.18/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.32  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.18/1.32  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.18/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.18/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.18/1.32  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.18/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.18/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.18/1.32  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.18/1.32  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.18/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.32  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.18/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.18/1.32  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.18/1.32  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.18/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.32  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.18/1.32  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.18/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.32  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.18/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.32  
% 2.55/1.34  tff(f_171, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.55/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.55/1.34  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 2.55/1.34  tff(f_153, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 2.55/1.34  tff(f_133, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.55/1.34  tff(f_97, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.55/1.34  tff(f_117, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.55/1.34  tff(f_75, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_orders_2)).
% 2.55/1.34  tff(c_58, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 2.55/1.34  tff(c_56, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 2.55/1.34  tff(c_54, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 2.55/1.34  tff(c_52, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 2.55/1.34  tff(c_50, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 2.55/1.34  tff(c_48, plain, (m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 2.55/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.55/1.34  tff(c_46, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_171])).
% 2.55/1.34  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.55/1.34  tff(c_82, plain, (![A_77, B_78]: (k3_tarski(A_77)!=k1_xboole_0 | ~r2_hidden(B_78, A_77) | k1_xboole_0=B_78)), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.55/1.34  tff(c_91, plain, (![A_79]: (k3_tarski(A_79)!=k1_xboole_0 | '#skF_1'(A_79)=k1_xboole_0 | k1_xboole_0=A_79)), inference(resolution, [status(thm)], [c_4, c_82])).
% 2.55/1.34  tff(c_99, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0 | k4_orders_2('#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_46, c_91])).
% 2.55/1.34  tff(c_101, plain, (k4_orders_2('#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_99])).
% 2.55/1.34  tff(c_142, plain, (![A_107, B_108]: (~v1_xboole_0(k4_orders_2(A_107, B_108)) | ~m1_orders_1(B_108, k1_orders_1(u1_struct_0(A_107))) | ~l1_orders_2(A_107) | ~v5_orders_2(A_107) | ~v4_orders_2(A_107) | ~v3_orders_2(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.55/1.34  tff(c_145, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_48, c_142])).
% 2.55/1.34  tff(c_148, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2, c_101, c_145])).
% 2.55/1.34  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_148])).
% 2.55/1.34  tff(c_152, plain, (k4_orders_2('#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_99])).
% 2.55/1.34  tff(c_151, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_99])).
% 2.55/1.34  tff(c_163, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7')) | k4_orders_2('#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_151, c_4])).
% 2.55/1.34  tff(c_166, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_152, c_163])).
% 2.55/1.34  tff(c_244, plain, (![D_159, A_160, B_161]: (m2_orders_2(D_159, A_160, B_161) | ~r2_hidden(D_159, k4_orders_2(A_160, B_161)) | ~m1_orders_1(B_161, k1_orders_1(u1_struct_0(A_160))) | ~l1_orders_2(A_160) | ~v5_orders_2(A_160) | ~v4_orders_2(A_160) | ~v3_orders_2(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.55/1.34  tff(c_248, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_166, c_244])).
% 2.55/1.34  tff(c_261, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_248])).
% 2.55/1.34  tff(c_262, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_58, c_261])).
% 2.55/1.34  tff(c_36, plain, (![C_66, A_63, B_64]: (v6_orders_2(C_66, A_63) | ~m2_orders_2(C_66, A_63, B_64) | ~m1_orders_1(B_64, k1_orders_1(u1_struct_0(A_63))) | ~l1_orders_2(A_63) | ~v5_orders_2(A_63) | ~v4_orders_2(A_63) | ~v3_orders_2(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.55/1.34  tff(c_269, plain, (v6_orders_2(k1_xboole_0, '#skF_6') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_262, c_36])).
% 2.55/1.34  tff(c_274, plain, (v6_orders_2(k1_xboole_0, '#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_269])).
% 2.55/1.34  tff(c_275, plain, (v6_orders_2(k1_xboole_0, '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_58, c_274])).
% 2.55/1.34  tff(c_276, plain, (![C_162, A_163, B_164]: (m1_subset_1(C_162, k1_zfmisc_1(u1_struct_0(A_163))) | ~m2_orders_2(C_162, A_163, B_164) | ~m1_orders_1(B_164, k1_orders_1(u1_struct_0(A_163))) | ~l1_orders_2(A_163) | ~v5_orders_2(A_163) | ~v4_orders_2(A_163) | ~v3_orders_2(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.55/1.34  tff(c_278, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_262, c_276])).
% 2.55/1.34  tff(c_281, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_278])).
% 2.55/1.34  tff(c_282, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_58, c_281])).
% 2.55/1.34  tff(c_304, plain, (![A_167, B_168]: (~m2_orders_2(k1_xboole_0, A_167, B_168) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_167))) | ~v6_orders_2(k1_xboole_0, A_167) | ~m1_orders_1(B_168, k1_orders_1(u1_struct_0(A_167))) | ~l1_orders_2(A_167) | ~v5_orders_2(A_167) | ~v4_orders_2(A_167) | ~v3_orders_2(A_167) | v2_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.55/1.34  tff(c_306, plain, (![B_168]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_168) | ~v6_orders_2(k1_xboole_0, '#skF_6') | ~m1_orders_1(B_168, k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_282, c_304])).
% 2.55/1.34  tff(c_309, plain, (![B_168]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_168) | ~m1_orders_1(B_168, k1_orders_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_275, c_306])).
% 2.55/1.34  tff(c_311, plain, (![B_169]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_169) | ~m1_orders_1(B_169, k1_orders_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_309])).
% 2.55/1.34  tff(c_314, plain, (~m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_48, c_311])).
% 2.55/1.34  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_262, c_314])).
% 2.55/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.34  
% 2.55/1.34  Inference rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Ref     : 0
% 2.55/1.34  #Sup     : 52
% 2.55/1.34  #Fact    : 0
% 2.55/1.34  #Define  : 0
% 2.55/1.34  #Split   : 1
% 2.55/1.34  #Chain   : 0
% 2.55/1.34  #Close   : 0
% 2.55/1.34  
% 2.55/1.34  Ordering : KBO
% 2.55/1.34  
% 2.55/1.34  Simplification rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Subsume      : 2
% 2.55/1.34  #Demod        : 61
% 2.55/1.34  #Tautology    : 21
% 2.55/1.34  #SimpNegUnit  : 17
% 2.55/1.34  #BackRed      : 1
% 2.55/1.34  
% 2.55/1.34  #Partial instantiations: 0
% 2.55/1.34  #Strategies tried      : 1
% 2.55/1.34  
% 2.55/1.34  Timing (in seconds)
% 2.55/1.34  ----------------------
% 2.55/1.34  Preprocessing        : 0.34
% 2.55/1.34  Parsing              : 0.18
% 2.55/1.34  CNF conversion       : 0.03
% 2.55/1.34  Main loop            : 0.23
% 2.55/1.34  Inferencing          : 0.08
% 2.55/1.34  Reduction            : 0.07
% 2.55/1.34  Demodulation         : 0.05
% 2.55/1.34  BG Simplification    : 0.02
% 2.55/1.34  Subsumption          : 0.04
% 2.55/1.34  Abstraction          : 0.01
% 2.55/1.34  MUC search           : 0.00
% 2.55/1.34  Cooper               : 0.00
% 2.55/1.34  Total                : 0.61
% 2.55/1.34  Index Insertion      : 0.00
% 2.55/1.34  Index Deletion       : 0.00
% 2.55/1.34  Index Matching       : 0.00
% 2.55/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
