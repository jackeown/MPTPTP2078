%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:34 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 219 expanded)
%              Number of leaves         :   36 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 338 expanded)
%              Number of equality atoms :   37 ( 143 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_struct_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_32,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_34,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = k2_subset_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_40,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_41,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_40])).

tff(c_22,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_76,plain,(
    ! [A_31] :
      ( v1_xboole_0(k1_struct_0(A_31))
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_81,plain,(
    ! [A_32] :
      ( k1_struct_0(A_32) = k1_xboole_0
      | ~ l1_struct_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_76,c_4])).

tff(c_86,plain,(
    ! [A_33] :
      ( k1_struct_0(A_33) = k1_xboole_0
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_22,c_81])).

tff(c_90,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_86])).

tff(c_99,plain,(
    ! [A_34] :
      ( k3_subset_1(u1_struct_0(A_34),k1_struct_0(A_34)) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_108,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_99])).

tff(c_111,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_108])).

tff(c_112,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_115,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_112])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_115])).

tff(c_120,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_16,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_207,plain,(
    ! [B_50,A_51] :
      ( v4_pre_topc(B_50,A_51)
      | ~ v1_xboole_0(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_214,plain,(
    ! [A_51] :
      ( v4_pre_topc(k1_xboole_0,A_51)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_16,c_207])).

tff(c_241,plain,(
    ! [A_54] :
      ( v4_pre_topc(k1_xboole_0,A_54)
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_214])).

tff(c_170,plain,(
    ! [A_45,B_46] :
      ( k2_pre_topc(A_45,B_46) = B_46
      | ~ v4_pre_topc(B_46,A_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_173,plain,(
    ! [B_46] :
      ( k2_pre_topc('#skF_1',B_46) = B_46
      | ~ v4_pre_topc(B_46,'#skF_1')
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_170])).

tff(c_195,plain,(
    ! [B_49] :
      ( k2_pre_topc('#skF_1',B_49) = B_49
      | ~ v4_pre_topc(B_49,'#skF_1')
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_173])).

tff(c_204,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_195])).

tff(c_206,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_244,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_241,c_206])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_244])).

tff(c_252,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_39,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_145,plain,(
    ! [A_42,B_43] :
      ( k3_subset_1(A_42,k3_subset_1(A_42,B_43)) = B_43
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_147,plain,(
    ! [A_8] : k3_subset_1(A_8,k3_subset_1(A_8,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_145])).

tff(c_151,plain,(
    ! [A_8] : k3_subset_1(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_147])).

tff(c_352,plain,(
    ! [A_64,B_65] :
      ( k3_subset_1(u1_struct_0(A_64),k2_pre_topc(A_64,k3_subset_1(u1_struct_0(A_64),B_65))) = k1_tops_1(A_64,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_368,plain,(
    ! [A_64] :
      ( k3_subset_1(u1_struct_0(A_64),k2_pre_topc(A_64,k1_xboole_0)) = k1_tops_1(A_64,u1_struct_0(A_64))
      | ~ m1_subset_1(u1_struct_0(A_64),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_352])).

tff(c_419,plain,(
    ! [A_67] :
      ( k3_subset_1(u1_struct_0(A_67),k2_pre_topc(A_67,k1_xboole_0)) = k1_tops_1(A_67,u1_struct_0(A_67))
      | ~ l1_pre_topc(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_368])).

tff(c_431,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k1_tops_1('#skF_1',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_419])).

tff(c_438,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_41,c_120,c_120,c_431])).

tff(c_440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:34:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.74  
% 2.95/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.74  %$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_struct_0 > k1_xboole_0 > #skF_1
% 2.95/1.74  
% 2.95/1.74  %Foreground sorts:
% 2.95/1.74  
% 2.95/1.74  
% 2.95/1.74  %Background operators:
% 2.95/1.74  
% 2.95/1.74  
% 2.95/1.74  %Foreground operators:
% 2.95/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.95/1.74  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.95/1.74  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.95/1.74  tff('#skF_1', type, '#skF_1': $i).
% 2.95/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.74  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.95/1.74  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.95/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.74  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.95/1.74  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.95/1.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.95/1.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.95/1.74  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.95/1.74  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.95/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.95/1.74  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.95/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.74  
% 2.95/1.77  tff(f_102, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 2.95/1.77  tff(f_32, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.95/1.77  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.95/1.77  tff(f_42, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.95/1.77  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.95/1.77  tff(f_69, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_struct_0)).
% 2.95/1.77  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.95/1.77  tff(f_73, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_pre_topc)).
% 2.95/1.77  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.95/1.77  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.95/1.77  tff(f_61, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.95/1.77  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.95/1.77  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.95/1.77  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.95/1.77  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 2.95/1.77  tff(c_34, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.95/1.77  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.95/1.77  tff(c_6, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.95/1.77  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.95/1.77  tff(c_14, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=k2_subset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.95/1.77  tff(c_40, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 2.95/1.77  tff(c_41, plain, (![A_7]: (k3_subset_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_40])).
% 2.95/1.77  tff(c_22, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.95/1.77  tff(c_76, plain, (![A_31]: (v1_xboole_0(k1_struct_0(A_31)) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.95/1.77  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.95/1.77  tff(c_81, plain, (![A_32]: (k1_struct_0(A_32)=k1_xboole_0 | ~l1_struct_0(A_32))), inference(resolution, [status(thm)], [c_76, c_4])).
% 2.95/1.77  tff(c_86, plain, (![A_33]: (k1_struct_0(A_33)=k1_xboole_0 | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_22, c_81])).
% 2.95/1.77  tff(c_90, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_86])).
% 2.95/1.77  tff(c_99, plain, (![A_34]: (k3_subset_1(u1_struct_0(A_34), k1_struct_0(A_34))=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.95/1.77  tff(c_108, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_99])).
% 2.95/1.77  tff(c_111, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_108])).
% 2.95/1.77  tff(c_112, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_111])).
% 2.95/1.77  tff(c_115, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_112])).
% 2.95/1.77  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_115])).
% 2.95/1.77  tff(c_120, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_111])).
% 2.95/1.77  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.95/1.77  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.95/1.77  tff(c_16, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.95/1.77  tff(c_207, plain, (![B_50, A_51]: (v4_pre_topc(B_50, A_51) | ~v1_xboole_0(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.95/1.77  tff(c_214, plain, (![A_51]: (v4_pre_topc(k1_xboole_0, A_51) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(resolution, [status(thm)], [c_16, c_207])).
% 2.95/1.77  tff(c_241, plain, (![A_54]: (v4_pre_topc(k1_xboole_0, A_54) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_214])).
% 2.95/1.77  tff(c_170, plain, (![A_45, B_46]: (k2_pre_topc(A_45, B_46)=B_46 | ~v4_pre_topc(B_46, A_45) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.95/1.77  tff(c_173, plain, (![B_46]: (k2_pre_topc('#skF_1', B_46)=B_46 | ~v4_pre_topc(B_46, '#skF_1') | ~m1_subset_1(B_46, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_120, c_170])).
% 2.95/1.77  tff(c_195, plain, (![B_49]: (k2_pre_topc('#skF_1', B_49)=B_49 | ~v4_pre_topc(B_49, '#skF_1') | ~m1_subset_1(B_49, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_173])).
% 2.95/1.77  tff(c_204, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_16, c_195])).
% 2.95/1.77  tff(c_206, plain, (~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(splitLeft, [status(thm)], [c_204])).
% 2.95/1.77  tff(c_244, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_241, c_206])).
% 2.95/1.77  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_244])).
% 2.95/1.77  tff(c_252, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_204])).
% 2.95/1.77  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.95/1.77  tff(c_39, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.95/1.77  tff(c_145, plain, (![A_42, B_43]: (k3_subset_1(A_42, k3_subset_1(A_42, B_43))=B_43 | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.95/1.77  tff(c_147, plain, (![A_8]: (k3_subset_1(A_8, k3_subset_1(A_8, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_145])).
% 2.95/1.77  tff(c_151, plain, (![A_8]: (k3_subset_1(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_41, c_147])).
% 2.95/1.77  tff(c_352, plain, (![A_64, B_65]: (k3_subset_1(u1_struct_0(A_64), k2_pre_topc(A_64, k3_subset_1(u1_struct_0(A_64), B_65)))=k1_tops_1(A_64, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.95/1.77  tff(c_368, plain, (![A_64]: (k3_subset_1(u1_struct_0(A_64), k2_pre_topc(A_64, k1_xboole_0))=k1_tops_1(A_64, u1_struct_0(A_64)) | ~m1_subset_1(u1_struct_0(A_64), k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(superposition, [status(thm), theory('equality')], [c_151, c_352])).
% 2.95/1.77  tff(c_419, plain, (![A_67]: (k3_subset_1(u1_struct_0(A_67), k2_pre_topc(A_67, k1_xboole_0))=k1_tops_1(A_67, u1_struct_0(A_67)) | ~l1_pre_topc(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_368])).
% 2.95/1.77  tff(c_431, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k1_tops_1('#skF_1', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_252, c_419])).
% 2.95/1.77  tff(c_438, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_41, c_120, c_120, c_431])).
% 2.95/1.77  tff(c_440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_438])).
% 3.16/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.77  
% 3.16/1.77  Inference rules
% 3.16/1.77  ----------------------
% 3.16/1.77  #Ref     : 0
% 3.16/1.77  #Sup     : 81
% 3.16/1.77  #Fact    : 0
% 3.16/1.77  #Define  : 0
% 3.16/1.77  #Split   : 3
% 3.16/1.77  #Chain   : 0
% 3.16/1.77  #Close   : 0
% 3.16/1.77  
% 3.16/1.77  Ordering : KBO
% 3.16/1.77  
% 3.16/1.77  Simplification rules
% 3.16/1.77  ----------------------
% 3.16/1.77  #Subsume      : 3
% 3.16/1.77  #Demod        : 57
% 3.16/1.77  #Tautology    : 36
% 3.16/1.77  #SimpNegUnit  : 4
% 3.16/1.77  #BackRed      : 0
% 3.16/1.77  
% 3.16/1.77  #Partial instantiations: 0
% 3.16/1.77  #Strategies tried      : 1
% 3.16/1.77  
% 3.16/1.77  Timing (in seconds)
% 3.16/1.77  ----------------------
% 3.18/1.77  Preprocessing        : 0.46
% 3.18/1.77  Parsing              : 0.25
% 3.18/1.77  CNF conversion       : 0.03
% 3.18/1.77  Main loop            : 0.41
% 3.18/1.77  Inferencing          : 0.16
% 3.18/1.77  Reduction            : 0.12
% 3.18/1.77  Demodulation         : 0.09
% 3.18/1.77  BG Simplification    : 0.02
% 3.18/1.77  Subsumption          : 0.06
% 3.18/1.77  Abstraction          : 0.02
% 3.18/1.77  MUC search           : 0.00
% 3.18/1.78  Cooper               : 0.00
% 3.18/1.78  Total                : 0.93
% 3.18/1.78  Index Insertion      : 0.00
% 3.18/1.78  Index Deletion       : 0.00
% 3.18/1.78  Index Matching       : 0.00
% 3.18/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
