%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:29 EST 2020

% Result     : Theorem 5.03s
% Output     : CNFRefutation 5.03s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 191 expanded)
%              Number of leaves         :   37 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          :  180 ( 478 expanded)
%              Number of equality atoms :   20 (  80 expanded)
%              Maximal formula depth    :   15 (   4 average)
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

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_97,axiom,(
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

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C] :
                  ( r2_hidden(C,B)
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_mcart_1)).

tff(f_128,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_81,axiom,(
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

tff(c_51,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_48,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_46,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_44,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_42,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_26,plain,(
    ! [A_26] :
      ( l1_struct_0(A_26)
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_63,plain,(
    ! [A_43] :
      ( u1_struct_0(A_43) = k2_struct_0(A_43)
      | ~ l1_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_69,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_orders_2(A_45) ) ),
    inference(resolution,[status(thm)],[c_26,c_63])).

tff(c_73,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_69])).

tff(c_203,plain,(
    ! [A_79,B_80] :
      ( k2_orders_2(A_79,B_80) = a_2_1_orders_2(A_79,B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_orders_2(A_79)
      | ~ v5_orders_2(A_79)
      | ~ v4_orders_2(A_79)
      | ~ v3_orders_2(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_214,plain,(
    ! [B_80] :
      ( k2_orders_2('#skF_4',B_80) = a_2_1_orders_2('#skF_4',B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_203])).

tff(c_222,plain,(
    ! [B_80] :
      ( k2_orders_2('#skF_4',B_80) = a_2_1_orders_2('#skF_4',B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_214])).

tff(c_234,plain,(
    ! [B_84] :
      ( k2_orders_2('#skF_4',B_84) = a_2_1_orders_2('#skF_4',B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_222])).

tff(c_249,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_51,c_234])).

tff(c_40,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_250,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_40])).

tff(c_12,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1985,plain,(
    ! [A_194,B_195,C_196] :
      ( m1_subset_1('#skF_2'(A_194,B_195,C_196),u1_struct_0(B_195))
      | ~ r2_hidden(A_194,a_2_1_orders_2(B_195,C_196))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(u1_struct_0(B_195)))
      | ~ l1_orders_2(B_195)
      | ~ v5_orders_2(B_195)
      | ~ v4_orders_2(B_195)
      | ~ v3_orders_2(B_195)
      | v2_struct_0(B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1990,plain,(
    ! [A_194,C_196] :
      ( m1_subset_1('#skF_2'(A_194,'#skF_4',C_196),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_194,a_2_1_orders_2('#skF_4',C_196))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_1985])).

tff(c_1993,plain,(
    ! [A_194,C_196] :
      ( m1_subset_1('#skF_2'(A_194,'#skF_4',C_196),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_194,a_2_1_orders_2('#skF_4',C_196))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_73,c_1990])).

tff(c_1994,plain,(
    ! [A_194,C_196] :
      ( m1_subset_1('#skF_2'(A_194,'#skF_4',C_196),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_194,a_2_1_orders_2('#skF_4',C_196))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1993])).

tff(c_78,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(u1_struct_0(A_46))
      | ~ l1_struct_0(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_81,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_78])).

tff(c_82,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_81])).

tff(c_83,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_87,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_83])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_87])).

tff(c_92,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2404,plain,(
    ! [B_230,A_231,C_232,E_233] :
      ( r2_orders_2(B_230,'#skF_2'(A_231,B_230,C_232),E_233)
      | ~ r2_hidden(E_233,C_232)
      | ~ m1_subset_1(E_233,u1_struct_0(B_230))
      | ~ r2_hidden(A_231,a_2_1_orders_2(B_230,C_232))
      | ~ m1_subset_1(C_232,k1_zfmisc_1(u1_struct_0(B_230)))
      | ~ l1_orders_2(B_230)
      | ~ v5_orders_2(B_230)
      | ~ v4_orders_2(B_230)
      | ~ v3_orders_2(B_230)
      | v2_struct_0(B_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2412,plain,(
    ! [A_231,C_232,E_233] :
      ( r2_orders_2('#skF_4','#skF_2'(A_231,'#skF_4',C_232),E_233)
      | ~ r2_hidden(E_233,C_232)
      | ~ m1_subset_1(E_233,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_231,a_2_1_orders_2('#skF_4',C_232))
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_2404])).

tff(c_2419,plain,(
    ! [A_231,C_232,E_233] :
      ( r2_orders_2('#skF_4','#skF_2'(A_231,'#skF_4',C_232),E_233)
      | ~ r2_hidden(E_233,C_232)
      | ~ m1_subset_1(E_233,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_231,a_2_1_orders_2('#skF_4',C_232))
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_73,c_2412])).

tff(c_2426,plain,(
    ! [A_234,C_235,E_236] :
      ( r2_orders_2('#skF_4','#skF_2'(A_234,'#skF_4',C_235),E_236)
      | ~ r2_hidden(E_236,C_235)
      | ~ m1_subset_1(E_236,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_234,a_2_1_orders_2('#skF_4',C_235))
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2419])).

tff(c_2630,plain,(
    ! [A_255,E_256] :
      ( r2_orders_2('#skF_4','#skF_2'(A_255,'#skF_4',k2_struct_0('#skF_4')),E_256)
      | ~ r2_hidden(E_256,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_256,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_255,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_51,c_2426])).

tff(c_20,plain,(
    ! [A_16,C_22] :
      ( ~ r2_orders_2(A_16,C_22,C_22)
      | ~ m1_subset_1(C_22,u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2638,plain,(
    ! [A_255] :
      ( ~ m1_subset_1('#skF_2'(A_255,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_255,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_255,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_255,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2630,c_20])).

tff(c_2649,plain,(
    ! [A_257] :
      ( ~ r2_hidden('#skF_2'(A_257,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_257,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_257,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_73,c_2638])).

tff(c_2652,plain,(
    ! [A_257] :
      ( ~ r2_hidden(A_257,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_257,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_2649])).

tff(c_2670,plain,(
    ! [A_260] :
      ( ~ r2_hidden(A_260,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_260,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2652])).

tff(c_2674,plain,(
    ! [A_194] :
      ( ~ r2_hidden(A_194,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1994,c_2670])).

tff(c_2680,plain,(
    ! [A_261] : ~ r2_hidden(A_261,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_2674])).

tff(c_2688,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_2680])).

tff(c_2694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_2688])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:45:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.03/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.03/1.92  
% 5.03/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.03/1.93  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 5.03/1.93  
% 5.03/1.93  %Foreground sorts:
% 5.03/1.93  
% 5.03/1.93  
% 5.03/1.93  %Background operators:
% 5.03/1.93  
% 5.03/1.93  
% 5.03/1.93  %Foreground operators:
% 5.03/1.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.03/1.93  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.03/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.03/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.03/1.93  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.03/1.93  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.03/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.03/1.93  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 5.03/1.93  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 5.03/1.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.03/1.93  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.03/1.93  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.03/1.93  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.03/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.03/1.93  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.03/1.93  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.03/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.03/1.93  tff('#skF_4', type, '#skF_4': $i).
% 5.03/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.03/1.93  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 5.03/1.93  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.03/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.03/1.93  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.03/1.93  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.03/1.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.03/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.03/1.93  
% 5.03/1.94  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.03/1.94  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.03/1.94  tff(f_142, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_orders_2)).
% 5.03/1.94  tff(f_101, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 5.03/1.94  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.03/1.94  tff(f_97, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 5.03/1.94  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C]: (r2_hidden(C, B) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_mcart_1)).
% 5.03/1.94  tff(f_128, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 5.03/1.94  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.03/1.94  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.03/1.94  tff(f_81, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 5.03/1.94  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.03/1.94  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.03/1.94  tff(c_51, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 5.03/1.94  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.03/1.94  tff(c_48, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.03/1.94  tff(c_46, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.03/1.94  tff(c_44, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.03/1.94  tff(c_42, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.03/1.94  tff(c_26, plain, (![A_26]: (l1_struct_0(A_26) | ~l1_orders_2(A_26))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.03/1.94  tff(c_63, plain, (![A_43]: (u1_struct_0(A_43)=k2_struct_0(A_43) | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.03/1.94  tff(c_69, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_orders_2(A_45))), inference(resolution, [status(thm)], [c_26, c_63])).
% 5.03/1.94  tff(c_73, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_69])).
% 5.03/1.94  tff(c_203, plain, (![A_79, B_80]: (k2_orders_2(A_79, B_80)=a_2_1_orders_2(A_79, B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_orders_2(A_79) | ~v5_orders_2(A_79) | ~v4_orders_2(A_79) | ~v3_orders_2(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.03/1.94  tff(c_214, plain, (![B_80]: (k2_orders_2('#skF_4', B_80)=a_2_1_orders_2('#skF_4', B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_203])).
% 5.03/1.94  tff(c_222, plain, (![B_80]: (k2_orders_2('#skF_4', B_80)=a_2_1_orders_2('#skF_4', B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_214])).
% 5.03/1.94  tff(c_234, plain, (![B_84]: (k2_orders_2('#skF_4', B_84)=a_2_1_orders_2('#skF_4', B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_222])).
% 5.03/1.94  tff(c_249, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_51, c_234])).
% 5.03/1.94  tff(c_40, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.03/1.94  tff(c_250, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_249, c_40])).
% 5.03/1.94  tff(c_12, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.03/1.94  tff(c_1985, plain, (![A_194, B_195, C_196]: (m1_subset_1('#skF_2'(A_194, B_195, C_196), u1_struct_0(B_195)) | ~r2_hidden(A_194, a_2_1_orders_2(B_195, C_196)) | ~m1_subset_1(C_196, k1_zfmisc_1(u1_struct_0(B_195))) | ~l1_orders_2(B_195) | ~v5_orders_2(B_195) | ~v4_orders_2(B_195) | ~v3_orders_2(B_195) | v2_struct_0(B_195))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.03/1.94  tff(c_1990, plain, (![A_194, C_196]: (m1_subset_1('#skF_2'(A_194, '#skF_4', C_196), k2_struct_0('#skF_4')) | ~r2_hidden(A_194, a_2_1_orders_2('#skF_4', C_196)) | ~m1_subset_1(C_196, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_1985])).
% 5.03/1.94  tff(c_1993, plain, (![A_194, C_196]: (m1_subset_1('#skF_2'(A_194, '#skF_4', C_196), k2_struct_0('#skF_4')) | ~r2_hidden(A_194, a_2_1_orders_2('#skF_4', C_196)) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_73, c_1990])).
% 5.03/1.94  tff(c_1994, plain, (![A_194, C_196]: (m1_subset_1('#skF_2'(A_194, '#skF_4', C_196), k2_struct_0('#skF_4')) | ~r2_hidden(A_194, a_2_1_orders_2('#skF_4', C_196)) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1993])).
% 5.03/1.94  tff(c_78, plain, (![A_46]: (~v1_xboole_0(u1_struct_0(A_46)) | ~l1_struct_0(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.03/1.94  tff(c_81, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_73, c_78])).
% 5.03/1.94  tff(c_82, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_81])).
% 5.03/1.94  tff(c_83, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_82])).
% 5.03/1.94  tff(c_87, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_26, c_83])).
% 5.03/1.94  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_87])).
% 5.03/1.94  tff(c_92, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_82])).
% 5.03/1.94  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.03/1.94  tff(c_2404, plain, (![B_230, A_231, C_232, E_233]: (r2_orders_2(B_230, '#skF_2'(A_231, B_230, C_232), E_233) | ~r2_hidden(E_233, C_232) | ~m1_subset_1(E_233, u1_struct_0(B_230)) | ~r2_hidden(A_231, a_2_1_orders_2(B_230, C_232)) | ~m1_subset_1(C_232, k1_zfmisc_1(u1_struct_0(B_230))) | ~l1_orders_2(B_230) | ~v5_orders_2(B_230) | ~v4_orders_2(B_230) | ~v3_orders_2(B_230) | v2_struct_0(B_230))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.03/1.94  tff(c_2412, plain, (![A_231, C_232, E_233]: (r2_orders_2('#skF_4', '#skF_2'(A_231, '#skF_4', C_232), E_233) | ~r2_hidden(E_233, C_232) | ~m1_subset_1(E_233, u1_struct_0('#skF_4')) | ~r2_hidden(A_231, a_2_1_orders_2('#skF_4', C_232)) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_2404])).
% 5.03/1.94  tff(c_2419, plain, (![A_231, C_232, E_233]: (r2_orders_2('#skF_4', '#skF_2'(A_231, '#skF_4', C_232), E_233) | ~r2_hidden(E_233, C_232) | ~m1_subset_1(E_233, k2_struct_0('#skF_4')) | ~r2_hidden(A_231, a_2_1_orders_2('#skF_4', C_232)) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_73, c_2412])).
% 5.03/1.94  tff(c_2426, plain, (![A_234, C_235, E_236]: (r2_orders_2('#skF_4', '#skF_2'(A_234, '#skF_4', C_235), E_236) | ~r2_hidden(E_236, C_235) | ~m1_subset_1(E_236, k2_struct_0('#skF_4')) | ~r2_hidden(A_234, a_2_1_orders_2('#skF_4', C_235)) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_2419])).
% 5.03/1.94  tff(c_2630, plain, (![A_255, E_256]: (r2_orders_2('#skF_4', '#skF_2'(A_255, '#skF_4', k2_struct_0('#skF_4')), E_256) | ~r2_hidden(E_256, k2_struct_0('#skF_4')) | ~m1_subset_1(E_256, k2_struct_0('#skF_4')) | ~r2_hidden(A_255, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_51, c_2426])).
% 5.03/1.94  tff(c_20, plain, (![A_16, C_22]: (~r2_orders_2(A_16, C_22, C_22) | ~m1_subset_1(C_22, u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.03/1.94  tff(c_2638, plain, (![A_255]: (~m1_subset_1('#skF_2'(A_255, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_255, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_255, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_255, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2630, c_20])).
% 5.03/1.94  tff(c_2649, plain, (![A_257]: (~r2_hidden('#skF_2'(A_257, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_257, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_257, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_73, c_2638])).
% 5.03/1.94  tff(c_2652, plain, (![A_257]: (~r2_hidden(A_257, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_257, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_2649])).
% 5.03/1.94  tff(c_2670, plain, (![A_260]: (~r2_hidden(A_260, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_260, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_92, c_2652])).
% 5.03/1.94  tff(c_2674, plain, (![A_194]: (~r2_hidden(A_194, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1994, c_2670])).
% 5.03/1.94  tff(c_2680, plain, (![A_261]: (~r2_hidden(A_261, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_2674])).
% 5.03/1.94  tff(c_2688, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_2680])).
% 5.03/1.94  tff(c_2694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_250, c_2688])).
% 5.03/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.03/1.94  
% 5.03/1.94  Inference rules
% 5.03/1.94  ----------------------
% 5.03/1.94  #Ref     : 0
% 5.03/1.94  #Sup     : 567
% 5.03/1.94  #Fact    : 0
% 5.03/1.94  #Define  : 0
% 5.03/1.94  #Split   : 17
% 5.03/1.94  #Chain   : 0
% 5.03/1.94  #Close   : 0
% 5.03/1.94  
% 5.03/1.94  Ordering : KBO
% 5.03/1.94  
% 5.03/1.94  Simplification rules
% 5.03/1.94  ----------------------
% 5.03/1.94  #Subsume      : 43
% 5.03/1.94  #Demod        : 637
% 5.03/1.94  #Tautology    : 175
% 5.03/1.94  #SimpNegUnit  : 60
% 5.03/1.94  #BackRed      : 20
% 5.03/1.94  
% 5.03/1.94  #Partial instantiations: 0
% 5.03/1.94  #Strategies tried      : 1
% 5.03/1.94  
% 5.03/1.94  Timing (in seconds)
% 5.03/1.94  ----------------------
% 5.03/1.94  Preprocessing        : 0.33
% 5.03/1.94  Parsing              : 0.18
% 5.03/1.94  CNF conversion       : 0.02
% 5.03/1.94  Main loop            : 0.84
% 5.03/1.94  Inferencing          : 0.29
% 5.03/1.94  Reduction            : 0.27
% 5.03/1.95  Demodulation         : 0.19
% 5.03/1.95  BG Simplification    : 0.04
% 5.03/1.95  Subsumption          : 0.18
% 5.03/1.95  Abstraction          : 0.05
% 5.03/1.95  MUC search           : 0.00
% 5.03/1.95  Cooper               : 0.00
% 5.03/1.95  Total                : 1.21
% 5.03/1.95  Index Insertion      : 0.00
% 5.03/1.95  Index Deletion       : 0.00
% 5.03/1.95  Index Matching       : 0.00
% 5.03/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
