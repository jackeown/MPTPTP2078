%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:34 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 174 expanded)
%              Number of leaves         :   40 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 255 expanded)
%              Number of equality atoms :   41 (  99 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_struct_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_40,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_42,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_50,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_100,axiom,(
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

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_42,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_30,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [A_5] : k1_subset_1(A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_subset_1(A_10)) = k2_subset_1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_48,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_subset_1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18])).

tff(c_49,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_32,plain,(
    ! [A_21] :
      ( v1_xboole_0(k1_struct_0(A_21))
      | ~ l1_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_79,plain,(
    ! [B_36,A_37] :
      ( ~ v1_xboole_0(B_36)
      | B_36 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_86,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_2,c_79])).

tff(c_96,plain,(
    ! [A_39] :
      ( k1_struct_0(A_39) = k1_xboole_0
      | ~ l1_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_32,c_86])).

tff(c_101,plain,(
    ! [A_40] :
      ( k1_struct_0(A_40) = k1_xboole_0
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_30,c_96])).

tff(c_105,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_101])).

tff(c_173,plain,(
    ! [A_55] :
      ( k3_subset_1(u1_struct_0(A_55),k1_struct_0(A_55)) = k2_struct_0(A_55)
      | ~ l1_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_182,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_173])).

tff(c_185,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_182])).

tff(c_186,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_189,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_186])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_189])).

tff(c_194,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_20,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_304,plain,(
    ! [B_73,A_74] :
      ( v4_pre_topc(B_73,A_74)
      | ~ v1_xboole_0(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_319,plain,(
    ! [A_74] :
      ( v4_pre_topc(k1_xboole_0,A_74)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_20,c_304])).

tff(c_326,plain,(
    ! [A_74] :
      ( v4_pre_topc(k1_xboole_0,A_74)
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_319])).

tff(c_390,plain,(
    ! [A_84,B_85] :
      ( k2_pre_topc(A_84,B_85) = B_85
      | ~ v4_pre_topc(B_85,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_411,plain,(
    ! [A_86] :
      ( k2_pre_topc(A_86,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_20,c_390])).

tff(c_416,plain,(
    ! [A_87] :
      ( k2_pre_topc(A_87,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_326,c_411])).

tff(c_419,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_416])).

tff(c_422,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_419])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_47,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_106,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_113,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(resolution,[status(thm)],[c_47,c_106])).

tff(c_125,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k1_xboole_0
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_133,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_113,c_125])).

tff(c_231,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,B_63) = k3_subset_1(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_237,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_subset_1(A_9,A_9) ),
    inference(resolution,[status(thm)],[c_47,c_231])).

tff(c_243,plain,(
    ! [A_9] : k3_subset_1(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_237])).

tff(c_577,plain,(
    ! [A_98,B_99] :
      ( k3_subset_1(u1_struct_0(A_98),k2_pre_topc(A_98,k3_subset_1(u1_struct_0(A_98),B_99))) = k1_tops_1(A_98,B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_593,plain,(
    ! [A_98] :
      ( k3_subset_1(u1_struct_0(A_98),k2_pre_topc(A_98,k1_xboole_0)) = k1_tops_1(A_98,u1_struct_0(A_98))
      | ~ m1_subset_1(u1_struct_0(A_98),k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_577])).

tff(c_663,plain,(
    ! [A_102] :
      ( k3_subset_1(u1_struct_0(A_102),k2_pre_topc(A_102,k1_xboole_0)) = k1_tops_1(A_102,u1_struct_0(A_102))
      | ~ l1_pre_topc(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_593])).

tff(c_675,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k1_tops_1('#skF_1',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_663])).

tff(c_682,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_194,c_194,c_49,c_675])).

tff(c_684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_682])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:01:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.34  
% 2.65/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.35  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_struct_0 > k1_xboole_0 > #skF_1
% 2.65/1.35  
% 2.65/1.35  %Foreground sorts:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Background operators:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Foreground operators:
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.65/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.65/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.65/1.35  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.65/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.65/1.35  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.35  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.65/1.35  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.65/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.65/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.65/1.35  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.65/1.35  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.65/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.65/1.35  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.65/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.35  
% 2.88/1.37  tff(f_114, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 2.88/1.37  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.88/1.37  tff(f_40, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.88/1.37  tff(f_42, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.88/1.37  tff(f_50, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.88/1.37  tff(f_81, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_struct_0)).
% 2.88/1.37  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.88/1.37  tff(f_38, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.88/1.37  tff(f_85, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_pre_topc)).
% 2.88/1.37  tff(f_52, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.88/1.37  tff(f_73, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.88/1.37  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.88/1.37  tff(f_48, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.88/1.37  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.88/1.37  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.88/1.37  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.88/1.37  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 2.88/1.37  tff(c_42, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.88/1.37  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.88/1.37  tff(c_30, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.88/1.37  tff(c_10, plain, (![A_5]: (k1_subset_1(A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.88/1.37  tff(c_12, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.88/1.37  tff(c_18, plain, (![A_10]: (k3_subset_1(A_10, k1_subset_1(A_10))=k2_subset_1(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.88/1.37  tff(c_48, plain, (![A_10]: (k3_subset_1(A_10, k1_subset_1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18])).
% 2.88/1.37  tff(c_49, plain, (![A_10]: (k3_subset_1(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_48])).
% 2.88/1.37  tff(c_32, plain, (![A_21]: (v1_xboole_0(k1_struct_0(A_21)) | ~l1_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.88/1.37  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.88/1.37  tff(c_79, plain, (![B_36, A_37]: (~v1_xboole_0(B_36) | B_36=A_37 | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.88/1.37  tff(c_86, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_2, c_79])).
% 2.88/1.37  tff(c_96, plain, (![A_39]: (k1_struct_0(A_39)=k1_xboole_0 | ~l1_struct_0(A_39))), inference(resolution, [status(thm)], [c_32, c_86])).
% 2.88/1.37  tff(c_101, plain, (![A_40]: (k1_struct_0(A_40)=k1_xboole_0 | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_30, c_96])).
% 2.88/1.37  tff(c_105, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_101])).
% 2.88/1.37  tff(c_173, plain, (![A_55]: (k3_subset_1(u1_struct_0(A_55), k1_struct_0(A_55))=k2_struct_0(A_55) | ~l1_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.88/1.37  tff(c_182, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_105, c_173])).
% 2.88/1.37  tff(c_185, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_182])).
% 2.88/1.37  tff(c_186, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_185])).
% 2.88/1.37  tff(c_189, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_186])).
% 2.88/1.37  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_189])).
% 2.88/1.37  tff(c_194, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_185])).
% 2.88/1.37  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.88/1.37  tff(c_20, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.88/1.37  tff(c_304, plain, (![B_73, A_74]: (v4_pre_topc(B_73, A_74) | ~v1_xboole_0(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.88/1.37  tff(c_319, plain, (![A_74]: (v4_pre_topc(k1_xboole_0, A_74) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(resolution, [status(thm)], [c_20, c_304])).
% 2.88/1.37  tff(c_326, plain, (![A_74]: (v4_pre_topc(k1_xboole_0, A_74) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_319])).
% 2.88/1.37  tff(c_390, plain, (![A_84, B_85]: (k2_pre_topc(A_84, B_85)=B_85 | ~v4_pre_topc(B_85, A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.88/1.37  tff(c_411, plain, (![A_86]: (k2_pre_topc(A_86, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_86) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_20, c_390])).
% 2.88/1.37  tff(c_416, plain, (![A_87]: (k2_pre_topc(A_87, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87))), inference(resolution, [status(thm)], [c_326, c_411])).
% 2.88/1.37  tff(c_419, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_416])).
% 2.88/1.37  tff(c_422, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_419])).
% 2.88/1.37  tff(c_16, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.88/1.37  tff(c_47, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 2.88/1.37  tff(c_106, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.88/1.37  tff(c_113, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(resolution, [status(thm)], [c_47, c_106])).
% 2.88/1.37  tff(c_125, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k1_xboole_0 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.88/1.37  tff(c_133, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_113, c_125])).
% 2.88/1.37  tff(c_231, plain, (![A_62, B_63]: (k4_xboole_0(A_62, B_63)=k3_subset_1(A_62, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.88/1.37  tff(c_237, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_subset_1(A_9, A_9))), inference(resolution, [status(thm)], [c_47, c_231])).
% 2.88/1.37  tff(c_243, plain, (![A_9]: (k3_subset_1(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_133, c_237])).
% 2.88/1.37  tff(c_577, plain, (![A_98, B_99]: (k3_subset_1(u1_struct_0(A_98), k2_pre_topc(A_98, k3_subset_1(u1_struct_0(A_98), B_99)))=k1_tops_1(A_98, B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.88/1.37  tff(c_593, plain, (![A_98]: (k3_subset_1(u1_struct_0(A_98), k2_pre_topc(A_98, k1_xboole_0))=k1_tops_1(A_98, u1_struct_0(A_98)) | ~m1_subset_1(u1_struct_0(A_98), k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(superposition, [status(thm), theory('equality')], [c_243, c_577])).
% 2.88/1.37  tff(c_663, plain, (![A_102]: (k3_subset_1(u1_struct_0(A_102), k2_pre_topc(A_102, k1_xboole_0))=k1_tops_1(A_102, u1_struct_0(A_102)) | ~l1_pre_topc(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_593])).
% 2.88/1.37  tff(c_675, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k1_tops_1('#skF_1', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_422, c_663])).
% 2.88/1.37  tff(c_682, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_194, c_194, c_49, c_675])).
% 2.88/1.37  tff(c_684, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_682])).
% 2.88/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.37  
% 2.88/1.37  Inference rules
% 2.88/1.37  ----------------------
% 2.88/1.37  #Ref     : 0
% 2.88/1.37  #Sup     : 131
% 2.88/1.37  #Fact    : 0
% 2.88/1.37  #Define  : 0
% 2.88/1.37  #Split   : 3
% 2.88/1.37  #Chain   : 0
% 2.88/1.37  #Close   : 0
% 2.88/1.37  
% 2.88/1.37  Ordering : KBO
% 2.88/1.37  
% 2.88/1.37  Simplification rules
% 2.88/1.37  ----------------------
% 2.88/1.37  #Subsume      : 11
% 2.88/1.37  #Demod        : 69
% 2.88/1.37  #Tautology    : 62
% 2.88/1.37  #SimpNegUnit  : 3
% 2.88/1.37  #BackRed      : 0
% 2.88/1.37  
% 2.88/1.37  #Partial instantiations: 0
% 2.88/1.37  #Strategies tried      : 1
% 2.88/1.37  
% 2.88/1.37  Timing (in seconds)
% 2.88/1.37  ----------------------
% 2.88/1.37  Preprocessing        : 0.32
% 2.88/1.37  Parsing              : 0.17
% 2.88/1.37  CNF conversion       : 0.02
% 2.88/1.37  Main loop            : 0.32
% 2.88/1.37  Inferencing          : 0.12
% 2.88/1.37  Reduction            : 0.10
% 2.88/1.37  Demodulation         : 0.07
% 2.88/1.37  BG Simplification    : 0.02
% 2.88/1.37  Subsumption          : 0.05
% 2.88/1.37  Abstraction          : 0.02
% 2.88/1.37  MUC search           : 0.00
% 2.88/1.37  Cooper               : 0.00
% 2.88/1.37  Total                : 0.67
% 2.88/1.37  Index Insertion      : 0.00
% 2.88/1.37  Index Deletion       : 0.00
% 2.88/1.37  Index Matching       : 0.00
% 2.88/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
