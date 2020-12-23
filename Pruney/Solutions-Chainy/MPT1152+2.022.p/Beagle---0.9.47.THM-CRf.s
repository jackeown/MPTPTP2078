%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:30 EST 2020

% Result     : Theorem 9.22s
% Output     : CNFRefutation 9.39s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 588 expanded)
%              Number of leaves         :   36 ( 211 expanded)
%              Depth                    :   20
%              Number of atoms          :  236 (1413 expanded)
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

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C] :
                  ( r2_hidden(C,B)
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_mcart_1)).

tff(f_156,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_96,axiom,(
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

tff(f_142,axiom,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_80,axiom,(
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

tff(f_111,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(c_10,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_1'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_42,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_26,plain,(
    ! [A_29] :
      ( l1_struct_0(A_29)
      | ~ l1_orders_2(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_53,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_59,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_orders_2(A_47) ) ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_63,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_14,plain,(
    ! [A_16] :
      ( m1_subset_1(k2_struct_0(A_16),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

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
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_48,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_46,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_44,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_3078,plain,(
    ! [A_312,B_313] :
      ( k2_orders_2(A_312,B_313) = a_2_1_orders_2(A_312,B_313)
      | ~ m1_subset_1(B_313,k1_zfmisc_1(u1_struct_0(A_312)))
      | ~ l1_orders_2(A_312)
      | ~ v5_orders_2(A_312)
      | ~ v4_orders_2(A_312)
      | ~ v3_orders_2(A_312)
      | v2_struct_0(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3081,plain,(
    ! [B_313] :
      ( k2_orders_2('#skF_4',B_313) = a_2_1_orders_2('#skF_4',B_313)
      | ~ m1_subset_1(B_313,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_3078])).

tff(c_3086,plain,(
    ! [B_313] :
      ( k2_orders_2('#skF_4',B_313) = a_2_1_orders_2('#skF_4',B_313)
      | ~ m1_subset_1(B_313,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_3081])).

tff(c_3089,plain,(
    ! [B_314] :
      ( k2_orders_2('#skF_4',B_314) = a_2_1_orders_2('#skF_4',B_314)
      | ~ m1_subset_1(B_314,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_3086])).

tff(c_3093,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_3089])).

tff(c_40,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_3094,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3093,c_40])).

tff(c_3319,plain,(
    ! [A_332,B_333,C_334] :
      ( m1_subset_1('#skF_2'(A_332,B_333,C_334),u1_struct_0(B_333))
      | ~ r2_hidden(A_332,a_2_1_orders_2(B_333,C_334))
      | ~ m1_subset_1(C_334,k1_zfmisc_1(u1_struct_0(B_333)))
      | ~ l1_orders_2(B_333)
      | ~ v5_orders_2(B_333)
      | ~ v4_orders_2(B_333)
      | ~ v3_orders_2(B_333)
      | v2_struct_0(B_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_3324,plain,(
    ! [A_332,C_334] :
      ( m1_subset_1('#skF_2'(A_332,'#skF_4',C_334),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_332,a_2_1_orders_2('#skF_4',C_334))
      | ~ m1_subset_1(C_334,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_3319])).

tff(c_3327,plain,(
    ! [A_332,C_334] :
      ( m1_subset_1('#skF_2'(A_332,'#skF_4',C_334),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_332,a_2_1_orders_2('#skF_4',C_334))
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_63,c_3324])).

tff(c_3328,plain,(
    ! [A_332,C_334] :
      ( m1_subset_1('#skF_2'(A_332,'#skF_4',C_334),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_332,a_2_1_orders_2('#skF_4',C_334))
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_3327])).

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

tff(c_3663,plain,(
    ! [B_351,A_352,C_353,E_354] :
      ( r2_orders_2(B_351,'#skF_2'(A_352,B_351,C_353),E_354)
      | ~ r2_hidden(E_354,C_353)
      | ~ m1_subset_1(E_354,u1_struct_0(B_351))
      | ~ r2_hidden(A_352,a_2_1_orders_2(B_351,C_353))
      | ~ m1_subset_1(C_353,k1_zfmisc_1(u1_struct_0(B_351)))
      | ~ l1_orders_2(B_351)
      | ~ v5_orders_2(B_351)
      | ~ v4_orders_2(B_351)
      | ~ v3_orders_2(B_351)
      | v2_struct_0(B_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_3667,plain,(
    ! [A_352,C_353,E_354] :
      ( r2_orders_2('#skF_4','#skF_2'(A_352,'#skF_4',C_353),E_354)
      | ~ r2_hidden(E_354,C_353)
      | ~ m1_subset_1(E_354,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_352,a_2_1_orders_2('#skF_4',C_353))
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_3663])).

tff(c_3672,plain,(
    ! [A_352,C_353,E_354] :
      ( r2_orders_2('#skF_4','#skF_2'(A_352,'#skF_4',C_353),E_354)
      | ~ r2_hidden(E_354,C_353)
      | ~ m1_subset_1(E_354,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_352,a_2_1_orders_2('#skF_4',C_353))
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_63,c_3667])).

tff(c_3886,plain,(
    ! [A_376,C_377,E_378] :
      ( r2_orders_2('#skF_4','#skF_2'(A_376,'#skF_4',C_377),E_378)
      | ~ r2_hidden(E_378,C_377)
      | ~ m1_subset_1(E_378,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_376,a_2_1_orders_2('#skF_4',C_377))
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_3672])).

tff(c_4115,plain,(
    ! [A_401,E_402] :
      ( r2_orders_2('#skF_4','#skF_2'(A_401,'#skF_4',k2_struct_0('#skF_4')),E_402)
      | ~ r2_hidden(E_402,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_402,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_401,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_80,c_3886])).

tff(c_18,plain,(
    ! [A_17,C_23] :
      ( ~ r2_orders_2(A_17,C_23,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4123,plain,(
    ! [A_401] :
      ( ~ m1_subset_1('#skF_2'(A_401,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_401,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_401,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_401,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_4115,c_18])).

tff(c_4137,plain,(
    ! [A_403] :
      ( ~ r2_hidden('#skF_2'(A_403,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_403,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_403,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_63,c_4123])).

tff(c_4143,plain,(
    ! [A_403] :
      ( ~ r2_hidden(A_403,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_403,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2,c_4137])).

tff(c_4147,plain,(
    ! [A_404] :
      ( ~ r2_hidden(A_404,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_404,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_4143])).

tff(c_4157,plain,(
    ! [A_332] :
      ( ~ r2_hidden(A_332,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_3328,c_4147])).

tff(c_4165,plain,(
    ! [A_405] : ~ r2_hidden(A_405,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4157])).

tff(c_4173,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_4165])).

tff(c_4179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3094,c_4173])).

tff(c_4193,plain,(
    ! [A_408] : ~ r2_hidden(A_408,k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_4204,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_4193])).

tff(c_4207,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_4204,c_80])).

tff(c_4208,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_63])).

tff(c_4344,plain,(
    ! [A_436,B_437] :
      ( k2_orders_2(A_436,B_437) = a_2_1_orders_2(A_436,B_437)
      | ~ m1_subset_1(B_437,k1_zfmisc_1(u1_struct_0(A_436)))
      | ~ l1_orders_2(A_436)
      | ~ v5_orders_2(A_436)
      | ~ v4_orders_2(A_436)
      | ~ v3_orders_2(A_436)
      | v2_struct_0(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4347,plain,(
    ! [B_437] :
      ( k2_orders_2('#skF_4',B_437) = a_2_1_orders_2('#skF_4',B_437)
      | ~ m1_subset_1(B_437,k1_zfmisc_1(k1_xboole_0))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4208,c_4344])).

tff(c_4352,plain,(
    ! [B_437] :
      ( k2_orders_2('#skF_4',B_437) = a_2_1_orders_2('#skF_4',B_437)
      | ~ m1_subset_1(B_437,k1_zfmisc_1(k1_xboole_0))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_4347])).

tff(c_4355,plain,(
    ! [B_438] :
      ( k2_orders_2('#skF_4',B_438) = a_2_1_orders_2('#skF_4',B_438)
      | ~ m1_subset_1(B_438,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_4352])).

tff(c_4359,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4207,c_4355])).

tff(c_4209,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_40])).

tff(c_4360,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4359,c_4209])).

tff(c_4181,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_4206,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_4181])).

tff(c_4380,plain,(
    ! [A_440,B_441] :
      ( m1_subset_1(k2_orders_2(A_440,B_441),k1_zfmisc_1(u1_struct_0(A_440)))
      | ~ m1_subset_1(B_441,k1_zfmisc_1(u1_struct_0(A_440)))
      | ~ l1_orders_2(A_440)
      | ~ v5_orders_2(A_440)
      | ~ v4_orders_2(A_440)
      | ~ v3_orders_2(A_440)
      | v2_struct_0(A_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4393,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4359,c_4380])).

tff(c_4401,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_4207,c_4208,c_4208,c_4393])).

tff(c_4402,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_4401])).

tff(c_4421,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_6,a_2_1_orders_2('#skF_4',k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_4402,c_6])).

tff(c_4427,plain,(
    ! [A_445] : ~ r2_hidden(A_445,a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4206,c_4421])).

tff(c_4435,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_4427])).

tff(c_4440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4360,c_4435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:36:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.22/3.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.22/3.21  
% 9.22/3.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.22/3.22  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 9.22/3.22  
% 9.22/3.22  %Foreground sorts:
% 9.22/3.22  
% 9.22/3.22  
% 9.22/3.22  %Background operators:
% 9.22/3.22  
% 9.22/3.22  
% 9.22/3.22  %Foreground operators:
% 9.22/3.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.22/3.22  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 9.22/3.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.22/3.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.22/3.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.22/3.22  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 9.22/3.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.22/3.22  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 9.22/3.22  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 9.22/3.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.22/3.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.22/3.22  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 9.22/3.22  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 9.22/3.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.22/3.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.22/3.22  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 9.22/3.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.22/3.22  tff('#skF_4', type, '#skF_4': $i).
% 9.22/3.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.22/3.22  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 9.22/3.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.22/3.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.22/3.22  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.22/3.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.22/3.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.22/3.22  
% 9.39/3.24  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C]: (r2_hidden(C, B) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_mcart_1)).
% 9.39/3.24  tff(f_156, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_orders_2)).
% 9.39/3.24  tff(f_115, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 9.39/3.24  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 9.39/3.24  tff(f_65, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 9.39/3.24  tff(f_96, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 9.39/3.24  tff(f_142, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 9.39/3.24  tff(f_44, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 9.39/3.24  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 9.39/3.24  tff(f_80, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 9.39/3.24  tff(f_111, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 9.39/3.24  tff(c_10, plain, (![A_9]: (r2_hidden('#skF_1'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.39/3.24  tff(c_42, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.39/3.24  tff(c_26, plain, (![A_29]: (l1_struct_0(A_29) | ~l1_orders_2(A_29))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.39/3.24  tff(c_53, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.39/3.24  tff(c_59, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_orders_2(A_47))), inference(resolution, [status(thm)], [c_26, c_53])).
% 9.39/3.24  tff(c_63, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_59])).
% 9.39/3.24  tff(c_14, plain, (![A_16]: (m1_subset_1(k2_struct_0(A_16), k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.39/3.24  tff(c_67, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_63, c_14])).
% 9.39/3.24  tff(c_72, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_67])).
% 9.39/3.24  tff(c_75, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_26, c_72])).
% 9.39/3.24  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_75])).
% 9.39/3.24  tff(c_80, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_67])).
% 9.39/3.24  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.39/3.24  tff(c_48, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.39/3.24  tff(c_46, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.39/3.24  tff(c_44, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.39/3.24  tff(c_3078, plain, (![A_312, B_313]: (k2_orders_2(A_312, B_313)=a_2_1_orders_2(A_312, B_313) | ~m1_subset_1(B_313, k1_zfmisc_1(u1_struct_0(A_312))) | ~l1_orders_2(A_312) | ~v5_orders_2(A_312) | ~v4_orders_2(A_312) | ~v3_orders_2(A_312) | v2_struct_0(A_312))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.39/3.24  tff(c_3081, plain, (![B_313]: (k2_orders_2('#skF_4', B_313)=a_2_1_orders_2('#skF_4', B_313) | ~m1_subset_1(B_313, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_3078])).
% 9.39/3.24  tff(c_3086, plain, (![B_313]: (k2_orders_2('#skF_4', B_313)=a_2_1_orders_2('#skF_4', B_313) | ~m1_subset_1(B_313, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_3081])).
% 9.39/3.24  tff(c_3089, plain, (![B_314]: (k2_orders_2('#skF_4', B_314)=a_2_1_orders_2('#skF_4', B_314) | ~m1_subset_1(B_314, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_3086])).
% 9.39/3.24  tff(c_3093, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_3089])).
% 9.39/3.24  tff(c_40, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.39/3.24  tff(c_3094, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3093, c_40])).
% 9.39/3.24  tff(c_3319, plain, (![A_332, B_333, C_334]: (m1_subset_1('#skF_2'(A_332, B_333, C_334), u1_struct_0(B_333)) | ~r2_hidden(A_332, a_2_1_orders_2(B_333, C_334)) | ~m1_subset_1(C_334, k1_zfmisc_1(u1_struct_0(B_333))) | ~l1_orders_2(B_333) | ~v5_orders_2(B_333) | ~v4_orders_2(B_333) | ~v3_orders_2(B_333) | v2_struct_0(B_333))), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.39/3.24  tff(c_3324, plain, (![A_332, C_334]: (m1_subset_1('#skF_2'(A_332, '#skF_4', C_334), k2_struct_0('#skF_4')) | ~r2_hidden(A_332, a_2_1_orders_2('#skF_4', C_334)) | ~m1_subset_1(C_334, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_3319])).
% 9.39/3.24  tff(c_3327, plain, (![A_332, C_334]: (m1_subset_1('#skF_2'(A_332, '#skF_4', C_334), k2_struct_0('#skF_4')) | ~r2_hidden(A_332, a_2_1_orders_2('#skF_4', C_334)) | ~m1_subset_1(C_334, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_63, c_3324])).
% 9.39/3.24  tff(c_3328, plain, (![A_332, C_334]: (m1_subset_1('#skF_2'(A_332, '#skF_4', C_334), k2_struct_0('#skF_4')) | ~r2_hidden(A_332, a_2_1_orders_2('#skF_4', C_334)) | ~m1_subset_1(C_334, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_3327])).
% 9.39/3.24  tff(c_6, plain, (![C_8, B_7, A_6]: (~v1_xboole_0(C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.39/3.24  tff(c_93, plain, (![A_6]: (~v1_xboole_0(k2_struct_0('#skF_4')) | ~r2_hidden(A_6, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_80, c_6])).
% 9.39/3.24  tff(c_94, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_93])).
% 9.39/3.24  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.39/3.24  tff(c_3663, plain, (![B_351, A_352, C_353, E_354]: (r2_orders_2(B_351, '#skF_2'(A_352, B_351, C_353), E_354) | ~r2_hidden(E_354, C_353) | ~m1_subset_1(E_354, u1_struct_0(B_351)) | ~r2_hidden(A_352, a_2_1_orders_2(B_351, C_353)) | ~m1_subset_1(C_353, k1_zfmisc_1(u1_struct_0(B_351))) | ~l1_orders_2(B_351) | ~v5_orders_2(B_351) | ~v4_orders_2(B_351) | ~v3_orders_2(B_351) | v2_struct_0(B_351))), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.39/3.24  tff(c_3667, plain, (![A_352, C_353, E_354]: (r2_orders_2('#skF_4', '#skF_2'(A_352, '#skF_4', C_353), E_354) | ~r2_hidden(E_354, C_353) | ~m1_subset_1(E_354, u1_struct_0('#skF_4')) | ~r2_hidden(A_352, a_2_1_orders_2('#skF_4', C_353)) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_3663])).
% 9.39/3.24  tff(c_3672, plain, (![A_352, C_353, E_354]: (r2_orders_2('#skF_4', '#skF_2'(A_352, '#skF_4', C_353), E_354) | ~r2_hidden(E_354, C_353) | ~m1_subset_1(E_354, k2_struct_0('#skF_4')) | ~r2_hidden(A_352, a_2_1_orders_2('#skF_4', C_353)) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_63, c_3667])).
% 9.39/3.24  tff(c_3886, plain, (![A_376, C_377, E_378]: (r2_orders_2('#skF_4', '#skF_2'(A_376, '#skF_4', C_377), E_378) | ~r2_hidden(E_378, C_377) | ~m1_subset_1(E_378, k2_struct_0('#skF_4')) | ~r2_hidden(A_376, a_2_1_orders_2('#skF_4', C_377)) | ~m1_subset_1(C_377, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_3672])).
% 9.39/3.24  tff(c_4115, plain, (![A_401, E_402]: (r2_orders_2('#skF_4', '#skF_2'(A_401, '#skF_4', k2_struct_0('#skF_4')), E_402) | ~r2_hidden(E_402, k2_struct_0('#skF_4')) | ~m1_subset_1(E_402, k2_struct_0('#skF_4')) | ~r2_hidden(A_401, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_80, c_3886])).
% 9.39/3.24  tff(c_18, plain, (![A_17, C_23]: (~r2_orders_2(A_17, C_23, C_23) | ~m1_subset_1(C_23, u1_struct_0(A_17)) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.39/3.24  tff(c_4123, plain, (![A_401]: (~m1_subset_1('#skF_2'(A_401, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_401, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_401, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_401, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_4115, c_18])).
% 9.39/3.24  tff(c_4137, plain, (![A_403]: (~r2_hidden('#skF_2'(A_403, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_403, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_403, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_63, c_4123])).
% 9.39/3.24  tff(c_4143, plain, (![A_403]: (~r2_hidden(A_403, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_403, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2, c_4137])).
% 9.39/3.24  tff(c_4147, plain, (![A_404]: (~r2_hidden(A_404, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_404, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_94, c_4143])).
% 9.39/3.24  tff(c_4157, plain, (![A_332]: (~r2_hidden(A_332, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_3328, c_4147])).
% 9.39/3.24  tff(c_4165, plain, (![A_405]: (~r2_hidden(A_405, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4157])).
% 9.39/3.24  tff(c_4173, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_4165])).
% 9.39/3.24  tff(c_4179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3094, c_4173])).
% 9.39/3.24  tff(c_4193, plain, (![A_408]: (~r2_hidden(A_408, k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_93])).
% 9.39/3.24  tff(c_4204, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_4193])).
% 9.39/3.24  tff(c_4207, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4204, c_4204, c_80])).
% 9.39/3.24  tff(c_4208, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4204, c_63])).
% 9.39/3.24  tff(c_4344, plain, (![A_436, B_437]: (k2_orders_2(A_436, B_437)=a_2_1_orders_2(A_436, B_437) | ~m1_subset_1(B_437, k1_zfmisc_1(u1_struct_0(A_436))) | ~l1_orders_2(A_436) | ~v5_orders_2(A_436) | ~v4_orders_2(A_436) | ~v3_orders_2(A_436) | v2_struct_0(A_436))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.39/3.24  tff(c_4347, plain, (![B_437]: (k2_orders_2('#skF_4', B_437)=a_2_1_orders_2('#skF_4', B_437) | ~m1_subset_1(B_437, k1_zfmisc_1(k1_xboole_0)) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4208, c_4344])).
% 9.39/3.24  tff(c_4352, plain, (![B_437]: (k2_orders_2('#skF_4', B_437)=a_2_1_orders_2('#skF_4', B_437) | ~m1_subset_1(B_437, k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_4347])).
% 9.39/3.24  tff(c_4355, plain, (![B_438]: (k2_orders_2('#skF_4', B_438)=a_2_1_orders_2('#skF_4', B_438) | ~m1_subset_1(B_438, k1_zfmisc_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_50, c_4352])).
% 9.39/3.24  tff(c_4359, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_4207, c_4355])).
% 9.39/3.24  tff(c_4209, plain, (k2_orders_2('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4204, c_40])).
% 9.39/3.24  tff(c_4360, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4359, c_4209])).
% 9.39/3.24  tff(c_4181, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_93])).
% 9.39/3.24  tff(c_4206, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4204, c_4181])).
% 9.39/3.24  tff(c_4380, plain, (![A_440, B_441]: (m1_subset_1(k2_orders_2(A_440, B_441), k1_zfmisc_1(u1_struct_0(A_440))) | ~m1_subset_1(B_441, k1_zfmisc_1(u1_struct_0(A_440))) | ~l1_orders_2(A_440) | ~v5_orders_2(A_440) | ~v4_orders_2(A_440) | ~v3_orders_2(A_440) | v2_struct_0(A_440))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.39/3.24  tff(c_4393, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4359, c_4380])).
% 9.39/3.24  tff(c_4401, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_4207, c_4208, c_4208, c_4393])).
% 9.39/3.24  tff(c_4402, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_50, c_4401])).
% 9.39/3.24  tff(c_4421, plain, (![A_6]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_6, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(resolution, [status(thm)], [c_4402, c_6])).
% 9.39/3.24  tff(c_4427, plain, (![A_445]: (~r2_hidden(A_445, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_4206, c_4421])).
% 9.39/3.24  tff(c_4435, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_4427])).
% 9.39/3.24  tff(c_4440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4360, c_4435])).
% 9.39/3.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.39/3.24  
% 9.39/3.24  Inference rules
% 9.39/3.24  ----------------------
% 9.39/3.24  #Ref     : 0
% 9.39/3.24  #Sup     : 872
% 9.39/3.24  #Fact    : 0
% 9.39/3.24  #Define  : 0
% 9.39/3.25  #Split   : 14
% 9.39/3.25  #Chain   : 0
% 9.39/3.25  #Close   : 0
% 9.39/3.25  
% 9.39/3.25  Ordering : KBO
% 9.39/3.25  
% 9.39/3.25  Simplification rules
% 9.39/3.25  ----------------------
% 9.39/3.25  #Subsume      : 166
% 9.39/3.25  #Demod        : 2070
% 9.39/3.25  #Tautology    : 292
% 9.39/3.25  #SimpNegUnit  : 211
% 9.39/3.25  #BackRed      : 42
% 9.39/3.25  
% 9.39/3.25  #Partial instantiations: 0
% 9.39/3.25  #Strategies tried      : 1
% 9.39/3.25  
% 9.39/3.25  Timing (in seconds)
% 9.39/3.25  ----------------------
% 9.39/3.25  Preprocessing        : 0.50
% 9.39/3.25  Parsing              : 0.24
% 9.39/3.25  CNF conversion       : 0.04
% 9.39/3.25  Main loop            : 1.94
% 9.39/3.25  Inferencing          : 0.73
% 9.39/3.25  Reduction            : 0.64
% 9.39/3.25  Demodulation         : 0.46
% 9.45/3.25  BG Simplification    : 0.07
% 9.45/3.25  Subsumption          : 0.36
% 9.45/3.25  Abstraction          : 0.09
% 9.45/3.25  MUC search           : 0.00
% 9.45/3.25  Cooper               : 0.00
% 9.45/3.25  Total                : 2.50
% 9.45/3.25  Index Insertion      : 0.00
% 9.45/3.25  Index Deletion       : 0.00
% 9.45/3.25  Index Matching       : 0.00
% 9.45/3.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
