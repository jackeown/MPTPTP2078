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
% DateTime   : Thu Dec  3 10:19:31 EST 2020

% Result     : Theorem 6.14s
% Output     : CNFRefutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 588 expanded)
%              Number of leaves         :   36 ( 211 expanded)
%              Depth                    :   20
%              Number of atoms          :  237 (1427 expanded)
%              Number of equality atoms :   28 ( 261 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_mcart_1)).

tff(f_158,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_98,axiom,(
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

tff(f_144,axiom,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_82,axiom,(
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

tff(f_113,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(c_10,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_1'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_26,plain,(
    ! [A_33] :
      ( l1_struct_0(A_33)
      | ~ l1_orders_2(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_53,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_59,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_orders_2(A_51) ) ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_63,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_14,plain,(
    ! [A_20] :
      ( m1_subset_1(k2_struct_0(A_20),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_67,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_14])).

tff(c_72,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_75,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_72])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_75])).

tff(c_80,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_48,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_46,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_44,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3445,plain,(
    ! [A_375,B_376] :
      ( k2_orders_2(A_375,B_376) = a_2_1_orders_2(A_375,B_376)
      | ~ m1_subset_1(B_376,k1_zfmisc_1(u1_struct_0(A_375)))
      | ~ l1_orders_2(A_375)
      | ~ v5_orders_2(A_375)
      | ~ v4_orders_2(A_375)
      | ~ v3_orders_2(A_375)
      | v2_struct_0(A_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3448,plain,(
    ! [B_376] :
      ( k2_orders_2('#skF_4',B_376) = a_2_1_orders_2('#skF_4',B_376)
      | ~ m1_subset_1(B_376,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_3445])).

tff(c_3453,plain,(
    ! [B_376] :
      ( k2_orders_2('#skF_4',B_376) = a_2_1_orders_2('#skF_4',B_376)
      | ~ m1_subset_1(B_376,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_3448])).

tff(c_3456,plain,(
    ! [B_377] :
      ( k2_orders_2('#skF_4',B_377) = a_2_1_orders_2('#skF_4',B_377)
      | ~ m1_subset_1(B_377,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_3453])).

tff(c_3460,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_3456])).

tff(c_40,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3461,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3460,c_40])).

tff(c_3666,plain,(
    ! [A_390,B_391,C_392] :
      ( m1_subset_1('#skF_2'(A_390,B_391,C_392),u1_struct_0(B_391))
      | ~ r2_hidden(A_390,a_2_1_orders_2(B_391,C_392))
      | ~ m1_subset_1(C_392,k1_zfmisc_1(u1_struct_0(B_391)))
      | ~ l1_orders_2(B_391)
      | ~ v5_orders_2(B_391)
      | ~ v4_orders_2(B_391)
      | ~ v3_orders_2(B_391)
      | v2_struct_0(B_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3671,plain,(
    ! [A_390,C_392] :
      ( m1_subset_1('#skF_2'(A_390,'#skF_4',C_392),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_390,a_2_1_orders_2('#skF_4',C_392))
      | ~ m1_subset_1(C_392,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_3666])).

tff(c_3674,plain,(
    ! [A_390,C_392] :
      ( m1_subset_1('#skF_2'(A_390,'#skF_4',C_392),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_390,a_2_1_orders_2('#skF_4',C_392))
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_63,c_3671])).

tff(c_3675,plain,(
    ! [A_390,C_392] :
      ( m1_subset_1('#skF_2'(A_390,'#skF_4',C_392),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_390,a_2_1_orders_2('#skF_4',C_392))
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_3674])).

tff(c_6,plain,(
    ! [C_8,B_7,A_6] :
      ( ~ v1_xboole_0(C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_93,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_6,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_80,c_6])).

tff(c_94,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4037,plain,(
    ! [B_413,A_414,C_415,E_416] :
      ( r2_orders_2(B_413,'#skF_2'(A_414,B_413,C_415),E_416)
      | ~ r2_hidden(E_416,C_415)
      | ~ m1_subset_1(E_416,u1_struct_0(B_413))
      | ~ r2_hidden(A_414,a_2_1_orders_2(B_413,C_415))
      | ~ m1_subset_1(C_415,k1_zfmisc_1(u1_struct_0(B_413)))
      | ~ l1_orders_2(B_413)
      | ~ v5_orders_2(B_413)
      | ~ v4_orders_2(B_413)
      | ~ v3_orders_2(B_413)
      | v2_struct_0(B_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_4041,plain,(
    ! [A_414,C_415,E_416] :
      ( r2_orders_2('#skF_4','#skF_2'(A_414,'#skF_4',C_415),E_416)
      | ~ r2_hidden(E_416,C_415)
      | ~ m1_subset_1(E_416,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_414,a_2_1_orders_2('#skF_4',C_415))
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_4037])).

tff(c_4046,plain,(
    ! [A_414,C_415,E_416] :
      ( r2_orders_2('#skF_4','#skF_2'(A_414,'#skF_4',C_415),E_416)
      | ~ r2_hidden(E_416,C_415)
      | ~ m1_subset_1(E_416,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_414,a_2_1_orders_2('#skF_4',C_415))
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_63,c_4041])).

tff(c_4176,plain,(
    ! [A_427,C_428,E_429] :
      ( r2_orders_2('#skF_4','#skF_2'(A_427,'#skF_4',C_428),E_429)
      | ~ r2_hidden(E_429,C_428)
      | ~ m1_subset_1(E_429,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_427,a_2_1_orders_2('#skF_4',C_428))
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_4046])).

tff(c_4469,plain,(
    ! [A_455,E_456] :
      ( r2_orders_2('#skF_4','#skF_2'(A_455,'#skF_4',k2_struct_0('#skF_4')),E_456)
      | ~ r2_hidden(E_456,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_456,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_455,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_80,c_4176])).

tff(c_18,plain,(
    ! [A_21,C_27] :
      ( ~ r2_orders_2(A_21,C_27,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_21))
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4477,plain,(
    ! [A_455] :
      ( ~ m1_subset_1('#skF_2'(A_455,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_455,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_455,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_455,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_4469,c_18])).

tff(c_4491,plain,(
    ! [A_457] :
      ( ~ r2_hidden('#skF_2'(A_457,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_457,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_457,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_63,c_4477])).

tff(c_4497,plain,(
    ! [A_457] :
      ( ~ r2_hidden(A_457,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_457,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2,c_4491])).

tff(c_4501,plain,(
    ! [A_458] :
      ( ~ r2_hidden(A_458,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_458,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_4497])).

tff(c_4511,plain,(
    ! [A_390] :
      ( ~ r2_hidden(A_390,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_3675,c_4501])).

tff(c_4520,plain,(
    ! [A_460] : ~ r2_hidden(A_460,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4511])).

tff(c_4528,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_4520])).

tff(c_4534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3461,c_4528])).

tff(c_4537,plain,(
    ! [A_461] : ~ r2_hidden(A_461,k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_4548,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_4537])).

tff(c_4551,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4548,c_4548,c_80])).

tff(c_4552,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4548,c_63])).

tff(c_4717,plain,(
    ! [A_502,B_503] :
      ( k2_orders_2(A_502,B_503) = a_2_1_orders_2(A_502,B_503)
      | ~ m1_subset_1(B_503,k1_zfmisc_1(u1_struct_0(A_502)))
      | ~ l1_orders_2(A_502)
      | ~ v5_orders_2(A_502)
      | ~ v4_orders_2(A_502)
      | ~ v3_orders_2(A_502)
      | v2_struct_0(A_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4720,plain,(
    ! [B_503] :
      ( k2_orders_2('#skF_4',B_503) = a_2_1_orders_2('#skF_4',B_503)
      | ~ m1_subset_1(B_503,k1_zfmisc_1(k1_xboole_0))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4552,c_4717])).

tff(c_4725,plain,(
    ! [B_503] :
      ( k2_orders_2('#skF_4',B_503) = a_2_1_orders_2('#skF_4',B_503)
      | ~ m1_subset_1(B_503,k1_zfmisc_1(k1_xboole_0))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_4720])).

tff(c_4728,plain,(
    ! [B_504] :
      ( k2_orders_2('#skF_4',B_504) = a_2_1_orders_2('#skF_4',B_504)
      | ~ m1_subset_1(B_504,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_4725])).

tff(c_4732,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4551,c_4728])).

tff(c_4553,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4548,c_40])).

tff(c_4733,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4732,c_4553])).

tff(c_4536,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_4550,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4548,c_4536])).

tff(c_4753,plain,(
    ! [A_506,B_507] :
      ( m1_subset_1(k2_orders_2(A_506,B_507),k1_zfmisc_1(u1_struct_0(A_506)))
      | ~ m1_subset_1(B_507,k1_zfmisc_1(u1_struct_0(A_506)))
      | ~ l1_orders_2(A_506)
      | ~ v5_orders_2(A_506)
      | ~ v4_orders_2(A_506)
      | ~ v3_orders_2(A_506)
      | v2_struct_0(A_506) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4766,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4732,c_4753])).

tff(c_4774,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_4551,c_4552,c_4552,c_4766])).

tff(c_4775,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_4774])).

tff(c_4794,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_6,a_2_1_orders_2('#skF_4',k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_4775,c_6])).

tff(c_4800,plain,(
    ! [A_511] : ~ r2_hidden(A_511,a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4550,c_4794])).

tff(c_4808,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_4800])).

tff(c_4813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4733,c_4808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:47:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.14/2.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.14/2.34  
% 6.14/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.14/2.35  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 6.14/2.35  
% 6.14/2.35  %Foreground sorts:
% 6.14/2.35  
% 6.14/2.35  
% 6.14/2.35  %Background operators:
% 6.14/2.35  
% 6.14/2.35  
% 6.14/2.35  %Foreground operators:
% 6.14/2.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.14/2.35  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.14/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.14/2.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.14/2.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.14/2.35  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 6.14/2.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.14/2.35  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 6.14/2.35  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 6.14/2.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.14/2.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.14/2.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.14/2.35  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.14/2.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.14/2.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.14/2.35  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.14/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.14/2.35  tff('#skF_4', type, '#skF_4': $i).
% 6.14/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.14/2.35  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 6.14/2.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.14/2.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.14/2.35  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.14/2.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.14/2.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.14/2.35  
% 6.41/2.36  tff(f_59, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ((r2_hidden(C, D) & r2_hidden(D, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_mcart_1)).
% 6.41/2.36  tff(f_158, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_orders_2)).
% 6.41/2.36  tff(f_117, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 6.41/2.36  tff(f_63, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 6.41/2.36  tff(f_67, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 6.41/2.36  tff(f_98, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 6.41/2.36  tff(f_144, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 6.41/2.36  tff(f_44, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 6.41/2.36  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 6.41/2.36  tff(f_82, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 6.41/2.36  tff(f_113, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 6.41/2.36  tff(c_10, plain, (![A_9]: (r2_hidden('#skF_1'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.41/2.36  tff(c_42, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.41/2.36  tff(c_26, plain, (![A_33]: (l1_struct_0(A_33) | ~l1_orders_2(A_33))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.41/2.36  tff(c_53, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.41/2.36  tff(c_59, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_orders_2(A_51))), inference(resolution, [status(thm)], [c_26, c_53])).
% 6.41/2.36  tff(c_63, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_59])).
% 6.41/2.36  tff(c_14, plain, (![A_20]: (m1_subset_1(k2_struct_0(A_20), k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.41/2.36  tff(c_67, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_63, c_14])).
% 6.41/2.36  tff(c_72, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_67])).
% 6.41/2.36  tff(c_75, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_26, c_72])).
% 6.41/2.36  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_75])).
% 6.41/2.36  tff(c_80, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_67])).
% 6.41/2.36  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.41/2.36  tff(c_48, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.41/2.36  tff(c_46, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.41/2.36  tff(c_44, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.41/2.36  tff(c_3445, plain, (![A_375, B_376]: (k2_orders_2(A_375, B_376)=a_2_1_orders_2(A_375, B_376) | ~m1_subset_1(B_376, k1_zfmisc_1(u1_struct_0(A_375))) | ~l1_orders_2(A_375) | ~v5_orders_2(A_375) | ~v4_orders_2(A_375) | ~v3_orders_2(A_375) | v2_struct_0(A_375))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.41/2.36  tff(c_3448, plain, (![B_376]: (k2_orders_2('#skF_4', B_376)=a_2_1_orders_2('#skF_4', B_376) | ~m1_subset_1(B_376, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_3445])).
% 6.41/2.36  tff(c_3453, plain, (![B_376]: (k2_orders_2('#skF_4', B_376)=a_2_1_orders_2('#skF_4', B_376) | ~m1_subset_1(B_376, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_3448])).
% 6.41/2.36  tff(c_3456, plain, (![B_377]: (k2_orders_2('#skF_4', B_377)=a_2_1_orders_2('#skF_4', B_377) | ~m1_subset_1(B_377, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_3453])).
% 6.41/2.36  tff(c_3460, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_3456])).
% 6.41/2.36  tff(c_40, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.41/2.36  tff(c_3461, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3460, c_40])).
% 6.41/2.36  tff(c_3666, plain, (![A_390, B_391, C_392]: (m1_subset_1('#skF_2'(A_390, B_391, C_392), u1_struct_0(B_391)) | ~r2_hidden(A_390, a_2_1_orders_2(B_391, C_392)) | ~m1_subset_1(C_392, k1_zfmisc_1(u1_struct_0(B_391))) | ~l1_orders_2(B_391) | ~v5_orders_2(B_391) | ~v4_orders_2(B_391) | ~v3_orders_2(B_391) | v2_struct_0(B_391))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.41/2.36  tff(c_3671, plain, (![A_390, C_392]: (m1_subset_1('#skF_2'(A_390, '#skF_4', C_392), k2_struct_0('#skF_4')) | ~r2_hidden(A_390, a_2_1_orders_2('#skF_4', C_392)) | ~m1_subset_1(C_392, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_3666])).
% 6.41/2.36  tff(c_3674, plain, (![A_390, C_392]: (m1_subset_1('#skF_2'(A_390, '#skF_4', C_392), k2_struct_0('#skF_4')) | ~r2_hidden(A_390, a_2_1_orders_2('#skF_4', C_392)) | ~m1_subset_1(C_392, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_63, c_3671])).
% 6.41/2.36  tff(c_3675, plain, (![A_390, C_392]: (m1_subset_1('#skF_2'(A_390, '#skF_4', C_392), k2_struct_0('#skF_4')) | ~r2_hidden(A_390, a_2_1_orders_2('#skF_4', C_392)) | ~m1_subset_1(C_392, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_3674])).
% 6.41/2.36  tff(c_6, plain, (![C_8, B_7, A_6]: (~v1_xboole_0(C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.41/2.36  tff(c_93, plain, (![A_6]: (~v1_xboole_0(k2_struct_0('#skF_4')) | ~r2_hidden(A_6, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_80, c_6])).
% 6.41/2.36  tff(c_94, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_93])).
% 6.41/2.36  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.41/2.36  tff(c_4037, plain, (![B_413, A_414, C_415, E_416]: (r2_orders_2(B_413, '#skF_2'(A_414, B_413, C_415), E_416) | ~r2_hidden(E_416, C_415) | ~m1_subset_1(E_416, u1_struct_0(B_413)) | ~r2_hidden(A_414, a_2_1_orders_2(B_413, C_415)) | ~m1_subset_1(C_415, k1_zfmisc_1(u1_struct_0(B_413))) | ~l1_orders_2(B_413) | ~v5_orders_2(B_413) | ~v4_orders_2(B_413) | ~v3_orders_2(B_413) | v2_struct_0(B_413))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.41/2.36  tff(c_4041, plain, (![A_414, C_415, E_416]: (r2_orders_2('#skF_4', '#skF_2'(A_414, '#skF_4', C_415), E_416) | ~r2_hidden(E_416, C_415) | ~m1_subset_1(E_416, u1_struct_0('#skF_4')) | ~r2_hidden(A_414, a_2_1_orders_2('#skF_4', C_415)) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_4037])).
% 6.41/2.36  tff(c_4046, plain, (![A_414, C_415, E_416]: (r2_orders_2('#skF_4', '#skF_2'(A_414, '#skF_4', C_415), E_416) | ~r2_hidden(E_416, C_415) | ~m1_subset_1(E_416, k2_struct_0('#skF_4')) | ~r2_hidden(A_414, a_2_1_orders_2('#skF_4', C_415)) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_63, c_4041])).
% 6.41/2.36  tff(c_4176, plain, (![A_427, C_428, E_429]: (r2_orders_2('#skF_4', '#skF_2'(A_427, '#skF_4', C_428), E_429) | ~r2_hidden(E_429, C_428) | ~m1_subset_1(E_429, k2_struct_0('#skF_4')) | ~r2_hidden(A_427, a_2_1_orders_2('#skF_4', C_428)) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_4046])).
% 6.41/2.36  tff(c_4469, plain, (![A_455, E_456]: (r2_orders_2('#skF_4', '#skF_2'(A_455, '#skF_4', k2_struct_0('#skF_4')), E_456) | ~r2_hidden(E_456, k2_struct_0('#skF_4')) | ~m1_subset_1(E_456, k2_struct_0('#skF_4')) | ~r2_hidden(A_455, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_80, c_4176])).
% 6.41/2.36  tff(c_18, plain, (![A_21, C_27]: (~r2_orders_2(A_21, C_27, C_27) | ~m1_subset_1(C_27, u1_struct_0(A_21)) | ~l1_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.41/2.36  tff(c_4477, plain, (![A_455]: (~m1_subset_1('#skF_2'(A_455, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_455, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_455, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_455, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_4469, c_18])).
% 6.41/2.36  tff(c_4491, plain, (![A_457]: (~r2_hidden('#skF_2'(A_457, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_457, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_457, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_63, c_4477])).
% 6.41/2.36  tff(c_4497, plain, (![A_457]: (~r2_hidden(A_457, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_457, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2, c_4491])).
% 6.41/2.36  tff(c_4501, plain, (![A_458]: (~r2_hidden(A_458, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_458, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_94, c_4497])).
% 6.41/2.36  tff(c_4511, plain, (![A_390]: (~r2_hidden(A_390, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_3675, c_4501])).
% 6.41/2.36  tff(c_4520, plain, (![A_460]: (~r2_hidden(A_460, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4511])).
% 6.41/2.36  tff(c_4528, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_4520])).
% 6.41/2.36  tff(c_4534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3461, c_4528])).
% 6.41/2.36  tff(c_4537, plain, (![A_461]: (~r2_hidden(A_461, k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_93])).
% 6.41/2.36  tff(c_4548, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_4537])).
% 6.41/2.36  tff(c_4551, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4548, c_4548, c_80])).
% 6.41/2.36  tff(c_4552, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4548, c_63])).
% 6.41/2.36  tff(c_4717, plain, (![A_502, B_503]: (k2_orders_2(A_502, B_503)=a_2_1_orders_2(A_502, B_503) | ~m1_subset_1(B_503, k1_zfmisc_1(u1_struct_0(A_502))) | ~l1_orders_2(A_502) | ~v5_orders_2(A_502) | ~v4_orders_2(A_502) | ~v3_orders_2(A_502) | v2_struct_0(A_502))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.41/2.36  tff(c_4720, plain, (![B_503]: (k2_orders_2('#skF_4', B_503)=a_2_1_orders_2('#skF_4', B_503) | ~m1_subset_1(B_503, k1_zfmisc_1(k1_xboole_0)) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4552, c_4717])).
% 6.41/2.36  tff(c_4725, plain, (![B_503]: (k2_orders_2('#skF_4', B_503)=a_2_1_orders_2('#skF_4', B_503) | ~m1_subset_1(B_503, k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_4720])).
% 6.41/2.36  tff(c_4728, plain, (![B_504]: (k2_orders_2('#skF_4', B_504)=a_2_1_orders_2('#skF_4', B_504) | ~m1_subset_1(B_504, k1_zfmisc_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_50, c_4725])).
% 6.41/2.36  tff(c_4732, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_4551, c_4728])).
% 6.41/2.36  tff(c_4553, plain, (k2_orders_2('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4548, c_40])).
% 6.41/2.36  tff(c_4733, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4732, c_4553])).
% 6.41/2.36  tff(c_4536, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_93])).
% 6.41/2.36  tff(c_4550, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4548, c_4536])).
% 6.41/2.36  tff(c_4753, plain, (![A_506, B_507]: (m1_subset_1(k2_orders_2(A_506, B_507), k1_zfmisc_1(u1_struct_0(A_506))) | ~m1_subset_1(B_507, k1_zfmisc_1(u1_struct_0(A_506))) | ~l1_orders_2(A_506) | ~v5_orders_2(A_506) | ~v4_orders_2(A_506) | ~v3_orders_2(A_506) | v2_struct_0(A_506))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.41/2.36  tff(c_4766, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4732, c_4753])).
% 6.41/2.36  tff(c_4774, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_4551, c_4552, c_4552, c_4766])).
% 6.41/2.36  tff(c_4775, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_50, c_4774])).
% 6.41/2.36  tff(c_4794, plain, (![A_6]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_6, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(resolution, [status(thm)], [c_4775, c_6])).
% 6.41/2.36  tff(c_4800, plain, (![A_511]: (~r2_hidden(A_511, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_4550, c_4794])).
% 6.41/2.36  tff(c_4808, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_4800])).
% 6.41/2.36  tff(c_4813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4733, c_4808])).
% 6.41/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/2.36  
% 6.41/2.36  Inference rules
% 6.41/2.36  ----------------------
% 6.41/2.36  #Ref     : 0
% 6.41/2.36  #Sup     : 954
% 6.41/2.36  #Fact    : 0
% 6.41/2.36  #Define  : 0
% 6.41/2.36  #Split   : 15
% 6.41/2.36  #Chain   : 0
% 6.41/2.36  #Close   : 0
% 6.41/2.36  
% 6.41/2.36  Ordering : KBO
% 6.41/2.36  
% 6.41/2.36  Simplification rules
% 6.41/2.36  ----------------------
% 6.41/2.36  #Subsume      : 188
% 6.41/2.36  #Demod        : 2214
% 6.41/2.36  #Tautology    : 288
% 6.41/2.36  #SimpNegUnit  : 225
% 6.41/2.36  #BackRed      : 46
% 6.41/2.36  
% 6.41/2.36  #Partial instantiations: 0
% 6.41/2.36  #Strategies tried      : 1
% 6.41/2.36  
% 6.41/2.36  Timing (in seconds)
% 6.41/2.36  ----------------------
% 6.41/2.37  Preprocessing        : 0.33
% 6.41/2.37  Parsing              : 0.17
% 6.41/2.37  CNF conversion       : 0.02
% 6.41/2.37  Main loop            : 1.15
% 6.41/2.37  Inferencing          : 0.43
% 6.41/2.37  Reduction            : 0.37
% 6.41/2.37  Demodulation         : 0.26
% 6.41/2.37  BG Simplification    : 0.04
% 6.41/2.37  Subsumption          : 0.22
% 6.41/2.37  Abstraction          : 0.05
% 6.41/2.37  MUC search           : 0.00
% 6.41/2.37  Cooper               : 0.00
% 6.41/2.37  Total                : 1.52
% 6.41/2.37  Index Insertion      : 0.00
% 6.41/2.37  Index Deletion       : 0.00
% 6.41/2.37  Index Matching       : 0.00
% 6.41/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
