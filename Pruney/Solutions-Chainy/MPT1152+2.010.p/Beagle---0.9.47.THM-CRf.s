%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:29 EST 2020

% Result     : Theorem 5.40s
% Output     : CNFRefutation 5.75s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 509 expanded)
%              Number of leaves         :   38 ( 204 expanded)
%              Depth                    :   17
%              Number of atoms          :  217 (1364 expanded)
%              Number of equality atoms :   24 ( 254 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_67,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_mcart_1)).

tff(f_148,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_50,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_48,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_46,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_44,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_28,plain,(
    ! [A_42] :
      ( l1_struct_0(A_42)
      | ~ l1_orders_2(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_66,plain,(
    ! [A_60] :
      ( u1_struct_0(A_60) = k2_struct_0(A_60)
      | ~ l1_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_71,plain,(
    ! [A_61] :
      ( u1_struct_0(A_61) = k2_struct_0(A_61)
      | ~ l1_orders_2(A_61) ) ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_75,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_240,plain,(
    ! [A_99,B_100] :
      ( k2_orders_2(A_99,B_100) = a_2_1_orders_2(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_orders_2(A_99)
      | ~ v5_orders_2(A_99)
      | ~ v4_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_255,plain,(
    ! [B_100] :
      ( k2_orders_2('#skF_4',B_100) = a_2_1_orders_2('#skF_4',B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_240])).

tff(c_264,plain,(
    ! [B_100] :
      ( k2_orders_2('#skF_4',B_100) = a_2_1_orders_2('#skF_4',B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_255])).

tff(c_374,plain,(
    ! [B_102] :
      ( k2_orders_2('#skF_4',B_102) = a_2_1_orders_2('#skF_4',B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_264])).

tff(c_394,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_53,c_374])).

tff(c_42,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_412,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_42])).

tff(c_14,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_1'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_545,plain,(
    ! [A_115,B_116,C_117] :
      ( m1_subset_1('#skF_2'(A_115,B_116,C_117),u1_struct_0(B_116))
      | ~ r2_hidden(A_115,a_2_1_orders_2(B_116,C_117))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(u1_struct_0(B_116)))
      | ~ l1_orders_2(B_116)
      | ~ v5_orders_2(B_116)
      | ~ v4_orders_2(B_116)
      | ~ v3_orders_2(B_116)
      | v2_struct_0(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_550,plain,(
    ! [A_115,C_117] :
      ( m1_subset_1('#skF_2'(A_115,'#skF_4',C_117),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_115,a_2_1_orders_2('#skF_4',C_117))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_545])).

tff(c_553,plain,(
    ! [A_115,C_117] :
      ( m1_subset_1('#skF_2'(A_115,'#skF_4',C_117),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_115,a_2_1_orders_2('#skF_4',C_117))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_75,c_550])).

tff(c_554,plain,(
    ! [A_115,C_117] :
      ( m1_subset_1('#skF_2'(A_115,'#skF_4',C_117),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_115,a_2_1_orders_2('#skF_4',C_117))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_553])).

tff(c_26,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k2_orders_2(A_40,B_41),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_orders_2(A_40)
      | ~ v5_orders_2(A_40)
      | ~ v4_orders_2(A_40)
      | ~ v3_orders_2(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_416,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_26])).

tff(c_420,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_53,c_75,c_75,c_416])).

tff(c_421,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_420])).

tff(c_10,plain,(
    ! [C_10,B_9,A_8] :
      ( ~ v1_xboole_0(C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_432,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_8,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_421,c_10])).

tff(c_449,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_432])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1061,plain,(
    ! [B_146,A_147,C_148,E_149] :
      ( r2_orders_2(B_146,'#skF_2'(A_147,B_146,C_148),E_149)
      | ~ r2_hidden(E_149,C_148)
      | ~ m1_subset_1(E_149,u1_struct_0(B_146))
      | ~ r2_hidden(A_147,a_2_1_orders_2(B_146,C_148))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0(B_146)))
      | ~ l1_orders_2(B_146)
      | ~ v5_orders_2(B_146)
      | ~ v4_orders_2(B_146)
      | ~ v3_orders_2(B_146)
      | v2_struct_0(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2712,plain,(
    ! [B_222,A_223,E_224] :
      ( r2_orders_2(B_222,'#skF_2'(A_223,B_222,u1_struct_0(B_222)),E_224)
      | ~ r2_hidden(E_224,u1_struct_0(B_222))
      | ~ m1_subset_1(E_224,u1_struct_0(B_222))
      | ~ r2_hidden(A_223,a_2_1_orders_2(B_222,u1_struct_0(B_222)))
      | ~ l1_orders_2(B_222)
      | ~ v5_orders_2(B_222)
      | ~ v4_orders_2(B_222)
      | ~ v3_orders_2(B_222)
      | v2_struct_0(B_222) ) ),
    inference(resolution,[status(thm)],[c_53,c_1061])).

tff(c_2723,plain,(
    ! [A_223,E_224] :
      ( r2_orders_2('#skF_4','#skF_2'(A_223,'#skF_4',k2_struct_0('#skF_4')),E_224)
      | ~ r2_hidden(E_224,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_224,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_223,a_2_1_orders_2('#skF_4',u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_2712])).

tff(c_2728,plain,(
    ! [A_223,E_224] :
      ( r2_orders_2('#skF_4','#skF_2'(A_223,'#skF_4',k2_struct_0('#skF_4')),E_224)
      | ~ r2_hidden(E_224,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_224,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_223,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_75,c_75,c_75,c_2723])).

tff(c_2749,plain,(
    ! [A_225,E_226] :
      ( r2_orders_2('#skF_4','#skF_2'(A_225,'#skF_4',k2_struct_0('#skF_4')),E_226)
      | ~ r2_hidden(E_226,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_226,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_225,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2728])).

tff(c_20,plain,(
    ! [A_30,C_36] :
      ( ~ r2_orders_2(A_30,C_36,C_36)
      | ~ m1_subset_1(C_36,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2757,plain,(
    ! [A_225] :
      ( ~ m1_subset_1('#skF_2'(A_225,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_225,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_225,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_225,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2749,c_20])).

tff(c_3327,plain,(
    ! [A_257] :
      ( ~ r2_hidden('#skF_2'(A_257,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_257,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_257,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_75,c_2757])).

tff(c_3336,plain,(
    ! [A_257] :
      ( ~ r2_hidden(A_257,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_257,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_3327])).

tff(c_3342,plain,(
    ! [A_258] :
      ( ~ r2_hidden(A_258,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_258,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_449,c_3336])).

tff(c_3352,plain,(
    ! [A_115] :
      ( ~ r2_hidden(A_115,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_554,c_3342])).

tff(c_3389,plain,(
    ! [A_263] : ~ r2_hidden(A_263,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_3352])).

tff(c_3397,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_3389])).

tff(c_3404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_412,c_3397])).

tff(c_3406,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_432])).

tff(c_81,plain,(
    ! [C_64,B_65,A_66] :
      ( ~ v1_xboole_0(C_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_86,plain,(
    ! [A_69,A_70] :
      ( ~ v1_xboole_0(A_69)
      | ~ r2_hidden(A_70,A_69) ) ),
    inference(resolution,[status(thm)],[c_53,c_81])).

tff(c_94,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_14,c_86])).

tff(c_3410,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3406,c_94])).

tff(c_3414,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3410,c_412])).

tff(c_3405,plain,(
    ! [A_8] : ~ r2_hidden(A_8,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_432])).

tff(c_3448,plain,(
    ! [A_264] : ~ r2_hidden(A_264,a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3410,c_3405])).

tff(c_3456,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_3448])).

tff(c_3461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3414,c_3456])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:26:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.40/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.40/2.07  
% 5.40/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.40/2.07  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 5.40/2.07  
% 5.40/2.07  %Foreground sorts:
% 5.40/2.07  
% 5.40/2.07  
% 5.40/2.07  %Background operators:
% 5.40/2.07  
% 5.40/2.07  
% 5.40/2.07  %Foreground operators:
% 5.40/2.07  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.40/2.07  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.40/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.40/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.40/2.07  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.40/2.07  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.40/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.40/2.07  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 5.40/2.07  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 5.40/2.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.40/2.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.40/2.07  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.40/2.07  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.40/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.40/2.07  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.40/2.07  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.40/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.40/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.40/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.40/2.07  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 5.40/2.07  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.40/2.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.40/2.07  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.40/2.07  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.40/2.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.40/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.40/2.07  
% 5.75/2.09  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.75/2.09  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.75/2.09  tff(f_162, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_orders_2)).
% 5.75/2.09  tff(f_121, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 5.75/2.09  tff(f_71, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.75/2.09  tff(f_102, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 5.75/2.09  tff(f_67, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_mcart_1)).
% 5.75/2.09  tff(f_148, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 5.75/2.09  tff(f_117, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 5.75/2.09  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.75/2.09  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.75/2.09  tff(f_86, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 5.75/2.09  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.75/2.09  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.75/2.09  tff(c_53, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 5.75/2.09  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.75/2.09  tff(c_50, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.75/2.09  tff(c_48, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.75/2.09  tff(c_46, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.75/2.09  tff(c_44, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.75/2.09  tff(c_28, plain, (![A_42]: (l1_struct_0(A_42) | ~l1_orders_2(A_42))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.75/2.09  tff(c_66, plain, (![A_60]: (u1_struct_0(A_60)=k2_struct_0(A_60) | ~l1_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.75/2.09  tff(c_71, plain, (![A_61]: (u1_struct_0(A_61)=k2_struct_0(A_61) | ~l1_orders_2(A_61))), inference(resolution, [status(thm)], [c_28, c_66])).
% 5.75/2.09  tff(c_75, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_71])).
% 5.75/2.09  tff(c_240, plain, (![A_99, B_100]: (k2_orders_2(A_99, B_100)=a_2_1_orders_2(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_orders_2(A_99) | ~v5_orders_2(A_99) | ~v4_orders_2(A_99) | ~v3_orders_2(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.75/2.09  tff(c_255, plain, (![B_100]: (k2_orders_2('#skF_4', B_100)=a_2_1_orders_2('#skF_4', B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_240])).
% 5.75/2.09  tff(c_264, plain, (![B_100]: (k2_orders_2('#skF_4', B_100)=a_2_1_orders_2('#skF_4', B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_255])).
% 5.75/2.09  tff(c_374, plain, (![B_102]: (k2_orders_2('#skF_4', B_102)=a_2_1_orders_2('#skF_4', B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_264])).
% 5.75/2.09  tff(c_394, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_53, c_374])).
% 5.75/2.09  tff(c_42, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.75/2.09  tff(c_412, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_394, c_42])).
% 5.75/2.09  tff(c_14, plain, (![A_11]: (r2_hidden('#skF_1'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.75/2.09  tff(c_545, plain, (![A_115, B_116, C_117]: (m1_subset_1('#skF_2'(A_115, B_116, C_117), u1_struct_0(B_116)) | ~r2_hidden(A_115, a_2_1_orders_2(B_116, C_117)) | ~m1_subset_1(C_117, k1_zfmisc_1(u1_struct_0(B_116))) | ~l1_orders_2(B_116) | ~v5_orders_2(B_116) | ~v4_orders_2(B_116) | ~v3_orders_2(B_116) | v2_struct_0(B_116))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.75/2.09  tff(c_550, plain, (![A_115, C_117]: (m1_subset_1('#skF_2'(A_115, '#skF_4', C_117), k2_struct_0('#skF_4')) | ~r2_hidden(A_115, a_2_1_orders_2('#skF_4', C_117)) | ~m1_subset_1(C_117, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_545])).
% 5.75/2.09  tff(c_553, plain, (![A_115, C_117]: (m1_subset_1('#skF_2'(A_115, '#skF_4', C_117), k2_struct_0('#skF_4')) | ~r2_hidden(A_115, a_2_1_orders_2('#skF_4', C_117)) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_75, c_550])).
% 5.75/2.09  tff(c_554, plain, (![A_115, C_117]: (m1_subset_1('#skF_2'(A_115, '#skF_4', C_117), k2_struct_0('#skF_4')) | ~r2_hidden(A_115, a_2_1_orders_2('#skF_4', C_117)) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_553])).
% 5.75/2.09  tff(c_26, plain, (![A_40, B_41]: (m1_subset_1(k2_orders_2(A_40, B_41), k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_orders_2(A_40) | ~v5_orders_2(A_40) | ~v4_orders_2(A_40) | ~v3_orders_2(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.75/2.09  tff(c_416, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_394, c_26])).
% 5.75/2.09  tff(c_420, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_53, c_75, c_75, c_416])).
% 5.75/2.09  tff(c_421, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_420])).
% 5.75/2.09  tff(c_10, plain, (![C_10, B_9, A_8]: (~v1_xboole_0(C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.75/2.09  tff(c_432, plain, (![A_8]: (~v1_xboole_0(k2_struct_0('#skF_4')) | ~r2_hidden(A_8, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_421, c_10])).
% 5.75/2.09  tff(c_449, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_432])).
% 5.75/2.09  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.75/2.09  tff(c_1061, plain, (![B_146, A_147, C_148, E_149]: (r2_orders_2(B_146, '#skF_2'(A_147, B_146, C_148), E_149) | ~r2_hidden(E_149, C_148) | ~m1_subset_1(E_149, u1_struct_0(B_146)) | ~r2_hidden(A_147, a_2_1_orders_2(B_146, C_148)) | ~m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0(B_146))) | ~l1_orders_2(B_146) | ~v5_orders_2(B_146) | ~v4_orders_2(B_146) | ~v3_orders_2(B_146) | v2_struct_0(B_146))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.75/2.09  tff(c_2712, plain, (![B_222, A_223, E_224]: (r2_orders_2(B_222, '#skF_2'(A_223, B_222, u1_struct_0(B_222)), E_224) | ~r2_hidden(E_224, u1_struct_0(B_222)) | ~m1_subset_1(E_224, u1_struct_0(B_222)) | ~r2_hidden(A_223, a_2_1_orders_2(B_222, u1_struct_0(B_222))) | ~l1_orders_2(B_222) | ~v5_orders_2(B_222) | ~v4_orders_2(B_222) | ~v3_orders_2(B_222) | v2_struct_0(B_222))), inference(resolution, [status(thm)], [c_53, c_1061])).
% 5.75/2.09  tff(c_2723, plain, (![A_223, E_224]: (r2_orders_2('#skF_4', '#skF_2'(A_223, '#skF_4', k2_struct_0('#skF_4')), E_224) | ~r2_hidden(E_224, u1_struct_0('#skF_4')) | ~m1_subset_1(E_224, u1_struct_0('#skF_4')) | ~r2_hidden(A_223, a_2_1_orders_2('#skF_4', u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_2712])).
% 5.75/2.09  tff(c_2728, plain, (![A_223, E_224]: (r2_orders_2('#skF_4', '#skF_2'(A_223, '#skF_4', k2_struct_0('#skF_4')), E_224) | ~r2_hidden(E_224, k2_struct_0('#skF_4')) | ~m1_subset_1(E_224, k2_struct_0('#skF_4')) | ~r2_hidden(A_223, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_75, c_75, c_75, c_2723])).
% 5.75/2.09  tff(c_2749, plain, (![A_225, E_226]: (r2_orders_2('#skF_4', '#skF_2'(A_225, '#skF_4', k2_struct_0('#skF_4')), E_226) | ~r2_hidden(E_226, k2_struct_0('#skF_4')) | ~m1_subset_1(E_226, k2_struct_0('#skF_4')) | ~r2_hidden(A_225, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_2728])).
% 5.75/2.09  tff(c_20, plain, (![A_30, C_36]: (~r2_orders_2(A_30, C_36, C_36) | ~m1_subset_1(C_36, u1_struct_0(A_30)) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.75/2.09  tff(c_2757, plain, (![A_225]: (~m1_subset_1('#skF_2'(A_225, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_225, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_225, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_225, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2749, c_20])).
% 5.75/2.09  tff(c_3327, plain, (![A_257]: (~r2_hidden('#skF_2'(A_257, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_257, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_257, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_75, c_2757])).
% 5.75/2.09  tff(c_3336, plain, (![A_257]: (~r2_hidden(A_257, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_257, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_3327])).
% 5.75/2.09  tff(c_3342, plain, (![A_258]: (~r2_hidden(A_258, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_258, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_449, c_3336])).
% 5.75/2.09  tff(c_3352, plain, (![A_115]: (~r2_hidden(A_115, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_554, c_3342])).
% 5.75/2.09  tff(c_3389, plain, (![A_263]: (~r2_hidden(A_263, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_3352])).
% 5.75/2.09  tff(c_3397, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_3389])).
% 5.75/2.09  tff(c_3404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_412, c_3397])).
% 5.75/2.09  tff(c_3406, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_432])).
% 5.75/2.09  tff(c_81, plain, (![C_64, B_65, A_66]: (~v1_xboole_0(C_64) | ~m1_subset_1(B_65, k1_zfmisc_1(C_64)) | ~r2_hidden(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.75/2.09  tff(c_86, plain, (![A_69, A_70]: (~v1_xboole_0(A_69) | ~r2_hidden(A_70, A_69))), inference(resolution, [status(thm)], [c_53, c_81])).
% 5.75/2.09  tff(c_94, plain, (![A_11]: (~v1_xboole_0(A_11) | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_14, c_86])).
% 5.75/2.09  tff(c_3410, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_3406, c_94])).
% 5.75/2.09  tff(c_3414, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3410, c_412])).
% 5.75/2.09  tff(c_3405, plain, (![A_8]: (~r2_hidden(A_8, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_432])).
% 5.75/2.09  tff(c_3448, plain, (![A_264]: (~r2_hidden(A_264, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_3410, c_3405])).
% 5.75/2.09  tff(c_3456, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_3448])).
% 5.75/2.09  tff(c_3461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3414, c_3456])).
% 5.75/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.09  
% 5.75/2.09  Inference rules
% 5.75/2.09  ----------------------
% 5.75/2.09  #Ref     : 0
% 5.75/2.09  #Sup     : 733
% 5.75/2.09  #Fact    : 0
% 5.75/2.09  #Define  : 0
% 5.75/2.09  #Split   : 17
% 5.75/2.09  #Chain   : 0
% 5.75/2.09  #Close   : 0
% 5.75/2.09  
% 5.75/2.09  Ordering : KBO
% 5.75/2.09  
% 5.75/2.09  Simplification rules
% 5.75/2.09  ----------------------
% 5.75/2.09  #Subsume      : 243
% 5.75/2.09  #Demod        : 1241
% 5.75/2.09  #Tautology    : 218
% 5.75/2.09  #SimpNegUnit  : 224
% 5.75/2.09  #BackRed      : 110
% 5.75/2.09  
% 5.75/2.09  #Partial instantiations: 0
% 5.75/2.09  #Strategies tried      : 1
% 5.75/2.09  
% 5.75/2.09  Timing (in seconds)
% 5.75/2.09  ----------------------
% 5.75/2.09  Preprocessing        : 0.35
% 5.75/2.09  Parsing              : 0.19
% 5.75/2.09  CNF conversion       : 0.02
% 5.75/2.09  Main loop            : 0.98
% 5.75/2.09  Inferencing          : 0.30
% 5.75/2.09  Reduction            : 0.35
% 5.75/2.09  Demodulation         : 0.24
% 5.75/2.09  BG Simplification    : 0.04
% 5.75/2.09  Subsumption          : 0.21
% 5.75/2.09  Abstraction          : 0.05
% 5.75/2.09  MUC search           : 0.00
% 5.75/2.09  Cooper               : 0.00
% 5.75/2.09  Total                : 1.36
% 5.75/2.09  Index Insertion      : 0.00
% 5.75/2.09  Index Deletion       : 0.00
% 5.75/2.09  Index Matching       : 0.00
% 5.75/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
