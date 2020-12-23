%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:47 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 130 expanded)
%              Number of leaves         :   43 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  119 ( 229 expanded)
%              Number of equality atoms :   34 (  57 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_103,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_90,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_48,plain,(
    ! [A_26] : l1_orders_2(k2_yellow_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_56,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_60,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_95,plain,(
    ! [D_41,B_42] : r2_hidden(D_41,k2_tarski(D_41,B_42)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    ! [D_43,B_44] : ~ v1_xboole_0(k2_tarski(D_43,B_44)) ),
    inference(resolution,[status(thm)],[c_95,c_2])).

tff(c_105,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_103])).

tff(c_253,plain,(
    ! [B_76,A_77] :
      ( m1_subset_1(k1_tarski(B_76),k1_zfmisc_1(A_77))
      | k1_xboole_0 = A_77
      | ~ m1_subset_1(B_76,A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_261,plain,(
    ! [B_76,A_77] :
      ( r1_tarski(k1_tarski(B_76),A_77)
      | k1_xboole_0 = A_77
      | ~ m1_subset_1(B_76,A_77) ) ),
    inference(resolution,[status(thm)],[c_253,c_32])).

tff(c_300,plain,(
    ! [B_83,A_84] :
      ( B_83 = A_84
      | ~ r1_tarski(A_84,B_83)
      | ~ v1_zfmisc_1(B_83)
      | v1_xboole_0(B_83)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_303,plain,(
    ! [B_76,A_77] :
      ( k1_tarski(B_76) = A_77
      | ~ v1_zfmisc_1(A_77)
      | v1_xboole_0(A_77)
      | v1_xboole_0(k1_tarski(B_76))
      | k1_xboole_0 = A_77
      | ~ m1_subset_1(B_76,A_77) ) ),
    inference(resolution,[status(thm)],[c_261,c_300])).

tff(c_390,plain,(
    ! [B_89,A_90] :
      ( k1_tarski(B_89) = A_90
      | ~ v1_zfmisc_1(A_90)
      | v1_xboole_0(A_90)
      | k1_xboole_0 = A_90
      | ~ m1_subset_1(B_89,A_90) ) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_303])).

tff(c_399,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_390])).

tff(c_404,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_399])).

tff(c_405,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_404])).

tff(c_406,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [B_51,A_52] :
      ( ~ r1_tarski(B_51,A_52)
      | ~ r2_hidden(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_157,plain,(
    ! [A_58] :
      ( ~ r1_tarski(A_58,'#skF_1'(A_58))
      | v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_4,c_131])).

tff(c_162,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_157])).

tff(c_412,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_162])).

tff(c_415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_412])).

tff(c_416,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_224,plain,(
    ! [A_72,B_73] :
      ( k6_domain_1(A_72,B_73) = k1_tarski(B_73)
      | ~ m1_subset_1(B_73,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_230,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_224])).

tff(c_234,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_230])).

tff(c_58,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_235,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_58])).

tff(c_418,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_235])).

tff(c_50,plain,(
    ! [A_27] : u1_struct_0(k2_yellow_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_126,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_164,plain,(
    ! [A_61] :
      ( u1_struct_0(A_61) = k2_struct_0(A_61)
      | ~ l1_orders_2(A_61) ) ),
    inference(resolution,[status(thm)],[c_42,c_126])).

tff(c_167,plain,(
    ! [A_26] : u1_struct_0(k2_yellow_1(A_26)) = k2_struct_0(k2_yellow_1(A_26)) ),
    inference(resolution,[status(thm)],[c_48,c_164])).

tff(c_169,plain,(
    ! [A_26] : k2_struct_0(k2_yellow_1(A_26)) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_167])).

tff(c_193,plain,(
    ! [A_67] :
      ( ~ v1_subset_1(k2_struct_0(A_67),u1_struct_0(A_67))
      | ~ l1_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_199,plain,(
    ! [A_27] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_27)),A_27)
      | ~ l1_struct_0(k2_yellow_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_193])).

tff(c_201,plain,(
    ! [A_27] :
      ( ~ v1_subset_1(A_27,A_27)
      | ~ l1_struct_0(k2_yellow_1(A_27)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_199])).

tff(c_446,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_418,c_201])).

tff(c_471,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_446])).

tff(c_475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_471])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:48:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.34  
% 2.27/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.34  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.27/1.34  
% 2.27/1.34  %Foreground sorts:
% 2.27/1.34  
% 2.27/1.34  
% 2.27/1.34  %Background operators:
% 2.27/1.34  
% 2.27/1.34  
% 2.27/1.34  %Foreground operators:
% 2.27/1.34  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.34  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.27/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.27/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.34  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.27/1.34  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.27/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.27/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.27/1.34  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.34  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.27/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.34  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.27/1.34  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.27/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.27/1.34  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.27/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.34  
% 2.69/1.36  tff(f_86, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.69/1.36  tff(f_75, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.69/1.36  tff(f_115, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.69/1.36  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.69/1.36  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.69/1.36  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.69/1.36  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.69/1.36  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.69/1.36  tff(f_103, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.69/1.36  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.69/1.36  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.69/1.36  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.69/1.36  tff(f_90, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.69/1.36  tff(f_66, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.69/1.36  tff(f_71, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.69/1.36  tff(c_48, plain, (![A_26]: (l1_orders_2(k2_yellow_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.69/1.36  tff(c_42, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.69/1.36  tff(c_62, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.69/1.36  tff(c_56, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.69/1.36  tff(c_60, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.69/1.36  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.69/1.36  tff(c_95, plain, (![D_41, B_42]: (r2_hidden(D_41, k2_tarski(D_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.69/1.36  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.36  tff(c_103, plain, (![D_43, B_44]: (~v1_xboole_0(k2_tarski(D_43, B_44)))), inference(resolution, [status(thm)], [c_95, c_2])).
% 2.69/1.36  tff(c_105, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_103])).
% 2.69/1.36  tff(c_253, plain, (![B_76, A_77]: (m1_subset_1(k1_tarski(B_76), k1_zfmisc_1(A_77)) | k1_xboole_0=A_77 | ~m1_subset_1(B_76, A_77))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.69/1.36  tff(c_32, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.36  tff(c_261, plain, (![B_76, A_77]: (r1_tarski(k1_tarski(B_76), A_77) | k1_xboole_0=A_77 | ~m1_subset_1(B_76, A_77))), inference(resolution, [status(thm)], [c_253, c_32])).
% 2.69/1.36  tff(c_300, plain, (![B_83, A_84]: (B_83=A_84 | ~r1_tarski(A_84, B_83) | ~v1_zfmisc_1(B_83) | v1_xboole_0(B_83) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.69/1.36  tff(c_303, plain, (![B_76, A_77]: (k1_tarski(B_76)=A_77 | ~v1_zfmisc_1(A_77) | v1_xboole_0(A_77) | v1_xboole_0(k1_tarski(B_76)) | k1_xboole_0=A_77 | ~m1_subset_1(B_76, A_77))), inference(resolution, [status(thm)], [c_261, c_300])).
% 2.69/1.36  tff(c_390, plain, (![B_89, A_90]: (k1_tarski(B_89)=A_90 | ~v1_zfmisc_1(A_90) | v1_xboole_0(A_90) | k1_xboole_0=A_90 | ~m1_subset_1(B_89, A_90))), inference(negUnitSimplification, [status(thm)], [c_105, c_303])).
% 2.69/1.36  tff(c_399, plain, (k1_tarski('#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_60, c_390])).
% 2.69/1.36  tff(c_404, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_399])).
% 2.69/1.36  tff(c_405, plain, (k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_62, c_404])).
% 2.69/1.36  tff(c_406, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_405])).
% 2.69/1.36  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.69/1.36  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.36  tff(c_131, plain, (![B_51, A_52]: (~r1_tarski(B_51, A_52) | ~r2_hidden(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.69/1.36  tff(c_157, plain, (![A_58]: (~r1_tarski(A_58, '#skF_1'(A_58)) | v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_4, c_131])).
% 2.69/1.36  tff(c_162, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_157])).
% 2.69/1.36  tff(c_412, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_406, c_162])).
% 2.69/1.36  tff(c_415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_412])).
% 2.69/1.36  tff(c_416, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_405])).
% 2.69/1.36  tff(c_224, plain, (![A_72, B_73]: (k6_domain_1(A_72, B_73)=k1_tarski(B_73) | ~m1_subset_1(B_73, A_72) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.69/1.36  tff(c_230, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_224])).
% 2.69/1.36  tff(c_234, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_230])).
% 2.69/1.36  tff(c_58, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.69/1.36  tff(c_235, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_58])).
% 2.69/1.36  tff(c_418, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_416, c_235])).
% 2.69/1.36  tff(c_50, plain, (![A_27]: (u1_struct_0(k2_yellow_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.69/1.36  tff(c_126, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.69/1.36  tff(c_164, plain, (![A_61]: (u1_struct_0(A_61)=k2_struct_0(A_61) | ~l1_orders_2(A_61))), inference(resolution, [status(thm)], [c_42, c_126])).
% 2.69/1.36  tff(c_167, plain, (![A_26]: (u1_struct_0(k2_yellow_1(A_26))=k2_struct_0(k2_yellow_1(A_26)))), inference(resolution, [status(thm)], [c_48, c_164])).
% 2.69/1.36  tff(c_169, plain, (![A_26]: (k2_struct_0(k2_yellow_1(A_26))=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_167])).
% 2.69/1.36  tff(c_193, plain, (![A_67]: (~v1_subset_1(k2_struct_0(A_67), u1_struct_0(A_67)) | ~l1_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.69/1.36  tff(c_199, plain, (![A_27]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_27)), A_27) | ~l1_struct_0(k2_yellow_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_193])).
% 2.69/1.36  tff(c_201, plain, (![A_27]: (~v1_subset_1(A_27, A_27) | ~l1_struct_0(k2_yellow_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_199])).
% 2.69/1.36  tff(c_446, plain, (~l1_struct_0(k2_yellow_1('#skF_4'))), inference(resolution, [status(thm)], [c_418, c_201])).
% 2.69/1.36  tff(c_471, plain, (~l1_orders_2(k2_yellow_1('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_446])).
% 2.69/1.36  tff(c_475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_471])).
% 2.69/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.36  
% 2.69/1.36  Inference rules
% 2.69/1.36  ----------------------
% 2.69/1.36  #Ref     : 0
% 2.69/1.36  #Sup     : 86
% 2.69/1.36  #Fact    : 2
% 2.69/1.36  #Define  : 0
% 2.69/1.36  #Split   : 1
% 2.69/1.36  #Chain   : 0
% 2.69/1.36  #Close   : 0
% 2.69/1.36  
% 2.69/1.36  Ordering : KBO
% 2.69/1.36  
% 2.69/1.36  Simplification rules
% 2.69/1.36  ----------------------
% 2.69/1.36  #Subsume      : 17
% 2.69/1.36  #Demod        : 33
% 2.69/1.36  #Tautology    : 39
% 2.69/1.36  #SimpNegUnit  : 15
% 2.69/1.36  #BackRed      : 10
% 2.69/1.36  
% 2.69/1.36  #Partial instantiations: 0
% 2.69/1.36  #Strategies tried      : 1
% 2.69/1.36  
% 2.69/1.36  Timing (in seconds)
% 2.69/1.36  ----------------------
% 2.69/1.36  Preprocessing        : 0.32
% 2.69/1.36  Parsing              : 0.17
% 2.69/1.36  CNF conversion       : 0.02
% 2.69/1.36  Main loop            : 0.26
% 2.69/1.36  Inferencing          : 0.09
% 2.69/1.36  Reduction            : 0.08
% 2.69/1.36  Demodulation         : 0.06
% 2.69/1.36  BG Simplification    : 0.02
% 2.69/1.36  Subsumption          : 0.04
% 2.69/1.36  Abstraction          : 0.02
% 2.69/1.36  MUC search           : 0.00
% 2.69/1.36  Cooper               : 0.00
% 2.69/1.36  Total                : 0.62
% 2.69/1.36  Index Insertion      : 0.00
% 2.69/1.36  Index Deletion       : 0.00
% 2.69/1.36  Index Matching       : 0.00
% 2.69/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
