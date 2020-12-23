%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:29 EST 2020

% Result     : Theorem 5.43s
% Output     : CNFRefutation 5.43s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 509 expanded)
%              Number of leaves         :   38 ( 204 expanded)
%              Depth                    :   17
%              Number of atoms          :  215 (1356 expanded)
%              Number of equality atoms :   25 ( 258 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_mcart_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_159,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_64,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_145,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_1_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_52,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_50,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_48,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_46,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_30,plain,(
    ! [A_42] :
      ( l1_struct_0(A_42)
      | ~ l1_orders_2(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_67,plain,(
    ! [A_59] :
      ( u1_struct_0(A_59) = k2_struct_0(A_59)
      | ~ l1_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_73,plain,(
    ! [A_61] :
      ( u1_struct_0(A_61) = k2_struct_0(A_61)
      | ~ l1_orders_2(A_61) ) ),
    inference(resolution,[status(thm)],[c_30,c_67])).

tff(c_77,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_73])).

tff(c_351,plain,(
    ! [A_114,B_115] :
      ( k2_orders_2(A_114,B_115) = a_2_1_orders_2(A_114,B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_orders_2(A_114)
      | ~ v5_orders_2(A_114)
      | ~ v4_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_366,plain,(
    ! [B_115] :
      ( k2_orders_2('#skF_4',B_115) = a_2_1_orders_2('#skF_4',B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_351])).

tff(c_375,plain,(
    ! [B_115] :
      ( k2_orders_2('#skF_4',B_115) = a_2_1_orders_2('#skF_4',B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_366])).

tff(c_398,plain,(
    ! [B_119] :
      ( k2_orders_2('#skF_4',B_119) = a_2_1_orders_2('#skF_4',B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_375])).

tff(c_418,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_55,c_398])).

tff(c_44,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_420,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_44])).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_1'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_569,plain,(
    ! [A_157,B_158,C_159] :
      ( m1_subset_1('#skF_2'(A_157,B_158,C_159),u1_struct_0(B_158))
      | ~ r2_hidden(A_157,a_2_1_orders_2(B_158,C_159))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(u1_struct_0(B_158)))
      | ~ l1_orders_2(B_158)
      | ~ v5_orders_2(B_158)
      | ~ v4_orders_2(B_158)
      | ~ v3_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_574,plain,(
    ! [A_157,C_159] :
      ( m1_subset_1('#skF_2'(A_157,'#skF_4',C_159),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_157,a_2_1_orders_2('#skF_4',C_159))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_569])).

tff(c_577,plain,(
    ! [A_157,C_159] :
      ( m1_subset_1('#skF_2'(A_157,'#skF_4',C_159),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_157,a_2_1_orders_2('#skF_4',C_159))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_77,c_574])).

tff(c_578,plain,(
    ! [A_157,C_159] :
      ( m1_subset_1('#skF_2'(A_157,'#skF_4',C_159),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_157,a_2_1_orders_2('#skF_4',C_159))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_577])).

tff(c_427,plain,(
    ! [A_123,B_124] :
      ( m1_subset_1(k2_orders_2(A_123,B_124),k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_orders_2(A_123)
      | ~ v5_orders_2(A_123)
      | ~ v4_orders_2(A_123)
      | ~ v3_orders_2(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_437,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_427])).

tff(c_445,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_55,c_77,c_77,c_437])).

tff(c_446,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_445])).

tff(c_10,plain,(
    ! [C_10,B_9,A_8] :
      ( ~ v1_xboole_0(C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_459,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_8,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_446,c_10])).

tff(c_460,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_459])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1082,plain,(
    ! [B_186,A_187,C_188,E_189] :
      ( r2_orders_2(B_186,'#skF_2'(A_187,B_186,C_188),E_189)
      | ~ r2_hidden(E_189,C_188)
      | ~ m1_subset_1(E_189,u1_struct_0(B_186))
      | ~ r2_hidden(A_187,a_2_1_orders_2(B_186,C_188))
      | ~ m1_subset_1(C_188,k1_zfmisc_1(u1_struct_0(B_186)))
      | ~ l1_orders_2(B_186)
      | ~ v5_orders_2(B_186)
      | ~ v4_orders_2(B_186)
      | ~ v3_orders_2(B_186)
      | v2_struct_0(B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2224,plain,(
    ! [B_250,A_251,E_252] :
      ( r2_orders_2(B_250,'#skF_2'(A_251,B_250,u1_struct_0(B_250)),E_252)
      | ~ r2_hidden(E_252,u1_struct_0(B_250))
      | ~ m1_subset_1(E_252,u1_struct_0(B_250))
      | ~ r2_hidden(A_251,a_2_1_orders_2(B_250,u1_struct_0(B_250)))
      | ~ l1_orders_2(B_250)
      | ~ v5_orders_2(B_250)
      | ~ v4_orders_2(B_250)
      | ~ v3_orders_2(B_250)
      | v2_struct_0(B_250) ) ),
    inference(resolution,[status(thm)],[c_55,c_1082])).

tff(c_2235,plain,(
    ! [A_251,E_252] :
      ( r2_orders_2('#skF_4','#skF_2'(A_251,'#skF_4',k2_struct_0('#skF_4')),E_252)
      | ~ r2_hidden(E_252,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_252,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_251,a_2_1_orders_2('#skF_4',u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_2224])).

tff(c_2240,plain,(
    ! [A_251,E_252] :
      ( r2_orders_2('#skF_4','#skF_2'(A_251,'#skF_4',k2_struct_0('#skF_4')),E_252)
      | ~ r2_hidden(E_252,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_252,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_251,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_77,c_77,c_77,c_2235])).

tff(c_2728,plain,(
    ! [A_287,E_288] :
      ( r2_orders_2('#skF_4','#skF_2'(A_287,'#skF_4',k2_struct_0('#skF_4')),E_288)
      | ~ r2_hidden(E_288,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_288,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_287,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2240])).

tff(c_22,plain,(
    ! [A_30,C_36] :
      ( ~ r2_orders_2(A_30,C_36,C_36)
      | ~ m1_subset_1(C_36,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2736,plain,(
    ! [A_287] :
      ( ~ m1_subset_1('#skF_2'(A_287,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_287,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_287,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_287,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2728,c_22])).

tff(c_3406,plain,(
    ! [A_328] :
      ( ~ r2_hidden('#skF_2'(A_328,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_328,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_328,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_77,c_2736])).

tff(c_3415,plain,(
    ! [A_328] :
      ( ~ r2_hidden(A_328,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_328,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_3406])).

tff(c_3421,plain,(
    ! [A_329] :
      ( ~ r2_hidden(A_329,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_329,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_460,c_3415])).

tff(c_3431,plain,(
    ! [A_157] :
      ( ~ r2_hidden(A_157,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_578,c_3421])).

tff(c_3440,plain,(
    ! [A_330] : ~ r2_hidden(A_330,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_3431])).

tff(c_3448,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_3440])).

tff(c_3455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_420,c_3448])).

tff(c_3457,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_83,plain,(
    ! [C_64,B_65,A_66] :
      ( ~ v1_xboole_0(C_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_88,plain,(
    ! [A_69,A_70] :
      ( ~ v1_xboole_0(A_69)
      | ~ r2_hidden(A_70,A_69) ) ),
    inference(resolution,[status(thm)],[c_55,c_83])).

tff(c_96,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_12,c_88])).

tff(c_3461,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3457,c_96])).

tff(c_3464,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3461,c_420])).

tff(c_3456,plain,(
    ! [A_8] : ~ r2_hidden(A_8,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_3519,plain,(
    ! [A_335] : ~ r2_hidden(A_335,a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3461,c_3456])).

tff(c_3527,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_3519])).

tff(c_3532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3464,c_3527])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:41:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.43/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.04  
% 5.43/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.04  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_mcart_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 5.43/2.04  
% 5.43/2.04  %Foreground sorts:
% 5.43/2.04  
% 5.43/2.04  
% 5.43/2.04  %Background operators:
% 5.43/2.04  
% 5.43/2.04  
% 5.43/2.04  %Foreground operators:
% 5.43/2.04  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.43/2.04  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.43/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.43/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.43/2.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.43/2.04  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.43/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.43/2.04  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 5.43/2.04  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 5.43/2.04  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.43/2.04  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.43/2.04  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.43/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.43/2.04  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.43/2.04  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.43/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.43/2.04  tff('#skF_4', type, '#skF_4': $i).
% 5.43/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.43/2.04  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 5.43/2.04  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.43/2.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.43/2.04  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 5.43/2.04  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.43/2.04  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.43/2.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.43/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.43/2.04  
% 5.43/2.05  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.43/2.05  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.43/2.05  tff(f_159, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_orders_2)).
% 5.43/2.05  tff(f_118, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 5.43/2.05  tff(f_68, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.43/2.05  tff(f_99, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 5.43/2.05  tff(f_64, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 5.43/2.05  tff(f_145, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 5.43/2.05  tff(f_114, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 5.43/2.05  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.43/2.05  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.43/2.05  tff(f_83, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 5.43/2.05  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.43/2.05  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.43/2.05  tff(c_55, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 5.43/2.05  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.43/2.05  tff(c_52, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.43/2.05  tff(c_50, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.43/2.05  tff(c_48, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.43/2.05  tff(c_46, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.43/2.05  tff(c_30, plain, (![A_42]: (l1_struct_0(A_42) | ~l1_orders_2(A_42))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.43/2.05  tff(c_67, plain, (![A_59]: (u1_struct_0(A_59)=k2_struct_0(A_59) | ~l1_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.43/2.05  tff(c_73, plain, (![A_61]: (u1_struct_0(A_61)=k2_struct_0(A_61) | ~l1_orders_2(A_61))), inference(resolution, [status(thm)], [c_30, c_67])).
% 5.43/2.05  tff(c_77, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_73])).
% 5.43/2.05  tff(c_351, plain, (![A_114, B_115]: (k2_orders_2(A_114, B_115)=a_2_1_orders_2(A_114, B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_orders_2(A_114) | ~v5_orders_2(A_114) | ~v4_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.43/2.05  tff(c_366, plain, (![B_115]: (k2_orders_2('#skF_4', B_115)=a_2_1_orders_2('#skF_4', B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_351])).
% 5.43/2.05  tff(c_375, plain, (![B_115]: (k2_orders_2('#skF_4', B_115)=a_2_1_orders_2('#skF_4', B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_366])).
% 5.43/2.05  tff(c_398, plain, (![B_119]: (k2_orders_2('#skF_4', B_119)=a_2_1_orders_2('#skF_4', B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_375])).
% 5.43/2.05  tff(c_418, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_55, c_398])).
% 5.43/2.05  tff(c_44, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.43/2.05  tff(c_420, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_418, c_44])).
% 5.43/2.05  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_1'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.43/2.05  tff(c_569, plain, (![A_157, B_158, C_159]: (m1_subset_1('#skF_2'(A_157, B_158, C_159), u1_struct_0(B_158)) | ~r2_hidden(A_157, a_2_1_orders_2(B_158, C_159)) | ~m1_subset_1(C_159, k1_zfmisc_1(u1_struct_0(B_158))) | ~l1_orders_2(B_158) | ~v5_orders_2(B_158) | ~v4_orders_2(B_158) | ~v3_orders_2(B_158) | v2_struct_0(B_158))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.43/2.05  tff(c_574, plain, (![A_157, C_159]: (m1_subset_1('#skF_2'(A_157, '#skF_4', C_159), k2_struct_0('#skF_4')) | ~r2_hidden(A_157, a_2_1_orders_2('#skF_4', C_159)) | ~m1_subset_1(C_159, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_569])).
% 5.43/2.05  tff(c_577, plain, (![A_157, C_159]: (m1_subset_1('#skF_2'(A_157, '#skF_4', C_159), k2_struct_0('#skF_4')) | ~r2_hidden(A_157, a_2_1_orders_2('#skF_4', C_159)) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_77, c_574])).
% 5.43/2.05  tff(c_578, plain, (![A_157, C_159]: (m1_subset_1('#skF_2'(A_157, '#skF_4', C_159), k2_struct_0('#skF_4')) | ~r2_hidden(A_157, a_2_1_orders_2('#skF_4', C_159)) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_577])).
% 5.43/2.05  tff(c_427, plain, (![A_123, B_124]: (m1_subset_1(k2_orders_2(A_123, B_124), k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_orders_2(A_123) | ~v5_orders_2(A_123) | ~v4_orders_2(A_123) | ~v3_orders_2(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.43/2.05  tff(c_437, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_418, c_427])).
% 5.43/2.05  tff(c_445, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_55, c_77, c_77, c_437])).
% 5.43/2.05  tff(c_446, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_445])).
% 5.43/2.05  tff(c_10, plain, (![C_10, B_9, A_8]: (~v1_xboole_0(C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.43/2.05  tff(c_459, plain, (![A_8]: (~v1_xboole_0(k2_struct_0('#skF_4')) | ~r2_hidden(A_8, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_446, c_10])).
% 5.43/2.05  tff(c_460, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_459])).
% 5.43/2.05  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.43/2.05  tff(c_1082, plain, (![B_186, A_187, C_188, E_189]: (r2_orders_2(B_186, '#skF_2'(A_187, B_186, C_188), E_189) | ~r2_hidden(E_189, C_188) | ~m1_subset_1(E_189, u1_struct_0(B_186)) | ~r2_hidden(A_187, a_2_1_orders_2(B_186, C_188)) | ~m1_subset_1(C_188, k1_zfmisc_1(u1_struct_0(B_186))) | ~l1_orders_2(B_186) | ~v5_orders_2(B_186) | ~v4_orders_2(B_186) | ~v3_orders_2(B_186) | v2_struct_0(B_186))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.43/2.05  tff(c_2224, plain, (![B_250, A_251, E_252]: (r2_orders_2(B_250, '#skF_2'(A_251, B_250, u1_struct_0(B_250)), E_252) | ~r2_hidden(E_252, u1_struct_0(B_250)) | ~m1_subset_1(E_252, u1_struct_0(B_250)) | ~r2_hidden(A_251, a_2_1_orders_2(B_250, u1_struct_0(B_250))) | ~l1_orders_2(B_250) | ~v5_orders_2(B_250) | ~v4_orders_2(B_250) | ~v3_orders_2(B_250) | v2_struct_0(B_250))), inference(resolution, [status(thm)], [c_55, c_1082])).
% 5.43/2.05  tff(c_2235, plain, (![A_251, E_252]: (r2_orders_2('#skF_4', '#skF_2'(A_251, '#skF_4', k2_struct_0('#skF_4')), E_252) | ~r2_hidden(E_252, u1_struct_0('#skF_4')) | ~m1_subset_1(E_252, u1_struct_0('#skF_4')) | ~r2_hidden(A_251, a_2_1_orders_2('#skF_4', u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_2224])).
% 5.43/2.05  tff(c_2240, plain, (![A_251, E_252]: (r2_orders_2('#skF_4', '#skF_2'(A_251, '#skF_4', k2_struct_0('#skF_4')), E_252) | ~r2_hidden(E_252, k2_struct_0('#skF_4')) | ~m1_subset_1(E_252, k2_struct_0('#skF_4')) | ~r2_hidden(A_251, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_77, c_77, c_77, c_2235])).
% 5.43/2.05  tff(c_2728, plain, (![A_287, E_288]: (r2_orders_2('#skF_4', '#skF_2'(A_287, '#skF_4', k2_struct_0('#skF_4')), E_288) | ~r2_hidden(E_288, k2_struct_0('#skF_4')) | ~m1_subset_1(E_288, k2_struct_0('#skF_4')) | ~r2_hidden(A_287, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_2240])).
% 5.43/2.05  tff(c_22, plain, (![A_30, C_36]: (~r2_orders_2(A_30, C_36, C_36) | ~m1_subset_1(C_36, u1_struct_0(A_30)) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.43/2.05  tff(c_2736, plain, (![A_287]: (~m1_subset_1('#skF_2'(A_287, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_287, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_287, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_287, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2728, c_22])).
% 5.43/2.05  tff(c_3406, plain, (![A_328]: (~r2_hidden('#skF_2'(A_328, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_328, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_328, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_77, c_2736])).
% 5.43/2.05  tff(c_3415, plain, (![A_328]: (~r2_hidden(A_328, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_328, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_3406])).
% 5.43/2.05  tff(c_3421, plain, (![A_329]: (~r2_hidden(A_329, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_329, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_460, c_3415])).
% 5.43/2.05  tff(c_3431, plain, (![A_157]: (~r2_hidden(A_157, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_578, c_3421])).
% 5.43/2.05  tff(c_3440, plain, (![A_330]: (~r2_hidden(A_330, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_3431])).
% 5.43/2.05  tff(c_3448, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_3440])).
% 5.43/2.05  tff(c_3455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_420, c_3448])).
% 5.43/2.05  tff(c_3457, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_459])).
% 5.43/2.05  tff(c_83, plain, (![C_64, B_65, A_66]: (~v1_xboole_0(C_64) | ~m1_subset_1(B_65, k1_zfmisc_1(C_64)) | ~r2_hidden(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.43/2.05  tff(c_88, plain, (![A_69, A_70]: (~v1_xboole_0(A_69) | ~r2_hidden(A_70, A_69))), inference(resolution, [status(thm)], [c_55, c_83])).
% 5.43/2.05  tff(c_96, plain, (![A_11]: (~v1_xboole_0(A_11) | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_12, c_88])).
% 5.43/2.05  tff(c_3461, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_3457, c_96])).
% 5.43/2.05  tff(c_3464, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3461, c_420])).
% 5.43/2.05  tff(c_3456, plain, (![A_8]: (~r2_hidden(A_8, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_459])).
% 5.43/2.05  tff(c_3519, plain, (![A_335]: (~r2_hidden(A_335, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_3461, c_3456])).
% 5.43/2.05  tff(c_3527, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_3519])).
% 5.43/2.05  tff(c_3532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3464, c_3527])).
% 5.43/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.05  
% 5.43/2.05  Inference rules
% 5.43/2.05  ----------------------
% 5.43/2.05  #Ref     : 0
% 5.43/2.05  #Sup     : 742
% 5.43/2.05  #Fact    : 0
% 5.43/2.05  #Define  : 0
% 5.43/2.05  #Split   : 17
% 5.43/2.05  #Chain   : 0
% 5.43/2.05  #Close   : 0
% 5.43/2.05  
% 5.43/2.05  Ordering : KBO
% 5.43/2.05  
% 5.43/2.05  Simplification rules
% 5.43/2.05  ----------------------
% 5.43/2.05  #Subsume      : 240
% 5.43/2.05  #Demod        : 1291
% 5.43/2.05  #Tautology    : 195
% 5.43/2.05  #SimpNegUnit  : 240
% 5.43/2.05  #BackRed      : 119
% 5.43/2.05  
% 5.43/2.05  #Partial instantiations: 0
% 5.43/2.05  #Strategies tried      : 1
% 5.43/2.05  
% 5.43/2.05  Timing (in seconds)
% 5.43/2.05  ----------------------
% 5.43/2.06  Preprocessing        : 0.33
% 5.43/2.06  Parsing              : 0.17
% 5.43/2.06  CNF conversion       : 0.02
% 5.43/2.06  Main loop            : 0.95
% 5.43/2.06  Inferencing          : 0.30
% 5.43/2.06  Reduction            : 0.35
% 5.43/2.06  Demodulation         : 0.24
% 5.43/2.06  BG Simplification    : 0.04
% 5.43/2.06  Subsumption          : 0.20
% 5.43/2.06  Abstraction          : 0.05
% 5.43/2.06  MUC search           : 0.00
% 5.43/2.06  Cooper               : 0.00
% 5.43/2.06  Total                : 1.32
% 5.43/2.06  Index Insertion      : 0.00
% 5.43/2.06  Index Deletion       : 0.00
% 5.43/2.06  Index Matching       : 0.00
% 5.43/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
