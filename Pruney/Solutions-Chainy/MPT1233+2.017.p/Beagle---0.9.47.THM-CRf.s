%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:32 EST 2020

% Result     : Theorem 5.77s
% Output     : CNFRefutation 5.89s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 134 expanded)
%              Number of leaves         :   44 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  120 ( 206 expanded)
%              Number of equality atoms :   40 (  72 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_mcart_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(f_80,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_44,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_46,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_52,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_44,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_3'(A_22),A_22)
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_139,plain,(
    ! [D_65,A_66,B_67] :
      ( r2_hidden(D_65,A_66)
      | ~ r2_hidden(D_65,k4_xboole_0(A_66,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_269,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_100,B_101)),A_100)
      | k4_xboole_0(A_100,B_101) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_139])).

tff(c_157,plain,(
    ! [D_70,B_71,A_72] :
      ( ~ r2_hidden(D_70,B_71)
      | ~ r2_hidden(D_70,k4_xboole_0(A_72,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_165,plain,(
    ! [A_72,B_71] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_72,B_71)),B_71)
      | k4_xboole_0(A_72,B_71) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_157])).

tff(c_298,plain,(
    ! [A_100] : k4_xboole_0(A_100,A_100) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_269,c_165])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_62,plain,(
    k1_tops_1('#skF_4',k2_struct_0('#skF_4')) != k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_28,plain,(
    ! [A_11] : k1_subset_1(A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_subset_1(A_15)) = k2_subset_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_67,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_subset_1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34])).

tff(c_68,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_67])).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_36,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_66,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_54,plain,(
    ! [A_40] :
      ( l1_struct_0(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_96,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_102,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_54,c_96])).

tff(c_106,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_102])).

tff(c_472,plain,(
    ! [B_124,A_125] :
      ( v4_pre_topc(B_124,A_125)
      | ~ v1_xboole_0(B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_487,plain,(
    ! [B_124] :
      ( v4_pre_topc(B_124,'#skF_4')
      | ~ v1_xboole_0(B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_472])).

tff(c_501,plain,(
    ! [B_127] :
      ( v4_pre_topc(B_127,'#skF_4')
      | ~ v1_xboole_0(B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_487])).

tff(c_517,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_4')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_501])).

tff(c_523,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_517])).

tff(c_593,plain,(
    ! [A_135,B_136] :
      ( k2_pre_topc(A_135,B_136) = B_136
      | ~ v4_pre_topc(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_619,plain,(
    ! [A_137] :
      ( k2_pre_topc(A_137,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_137)
      | ~ l1_pre_topc(A_137) ) ),
    inference(resolution,[status(thm)],[c_36,c_593])).

tff(c_622,plain,
    ( k2_pre_topc('#skF_4',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_523,c_619])).

tff(c_628,plain,(
    k2_pre_topc('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_622])).

tff(c_177,plain,(
    ! [A_76,B_77] :
      ( k3_subset_1(A_76,k3_subset_1(A_76,B_77)) = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_181,plain,(
    ! [A_16] : k3_subset_1(A_16,k3_subset_1(A_16,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_177])).

tff(c_184,plain,(
    ! [A_16] : k3_subset_1(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_181])).

tff(c_1986,plain,(
    ! [A_234,B_235] :
      ( k3_subset_1(u1_struct_0(A_234),k2_pre_topc(A_234,k3_subset_1(u1_struct_0(A_234),B_235))) = k1_tops_1(A_234,B_235)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ l1_pre_topc(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2016,plain,(
    ! [B_235] :
      ( k3_subset_1(k2_struct_0('#skF_4'),k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),B_235))) = k1_tops_1('#skF_4',B_235)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_1986])).

tff(c_2065,plain,(
    ! [B_237] :
      ( k3_subset_1(k2_struct_0('#skF_4'),k2_pre_topc('#skF_4',k3_subset_1(k2_struct_0('#skF_4'),B_237))) = k1_tops_1('#skF_4',B_237)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_106,c_106,c_2016])).

tff(c_2095,plain,
    ( k3_subset_1(k2_struct_0('#skF_4'),k2_pre_topc('#skF_4',k1_xboole_0)) = k1_tops_1('#skF_4',k2_struct_0('#skF_4'))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_2065])).

tff(c_2102,plain,
    ( k1_tops_1('#skF_4',k2_struct_0('#skF_4')) = k2_struct_0('#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_628,c_2095])).

tff(c_2103,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2102])).

tff(c_2109,plain,(
    ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_2103])).

tff(c_2112,plain,(
    k4_xboole_0(k2_struct_0('#skF_4'),k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_2109])).

tff(c_2116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_2112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:58:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.77/3.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/3.34  
% 5.89/3.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/3.34  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_mcart_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 5.89/3.34  
% 5.89/3.34  %Foreground sorts:
% 5.89/3.34  
% 5.89/3.34  
% 5.89/3.34  %Background operators:
% 5.89/3.34  
% 5.89/3.34  
% 5.89/3.34  %Foreground operators:
% 5.89/3.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.89/3.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.89/3.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.89/3.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.89/3.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.89/3.34  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.89/3.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.89/3.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.89/3.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.89/3.34  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.89/3.34  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.89/3.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.89/3.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.89/3.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.89/3.34  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.89/3.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.89/3.34  tff('#skF_4', type, '#skF_4': $i).
% 5.89/3.34  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.89/3.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.89/3.34  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 5.89/3.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.89/3.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.89/3.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.89/3.34  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.89/3.34  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.89/3.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.89/3.34  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.89/3.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.89/3.34  
% 5.89/3.39  tff(f_80, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 5.89/3.39  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.89/3.39  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.89/3.39  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.89/3.39  tff(f_128, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 5.89/3.39  tff(f_44, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 5.89/3.39  tff(f_46, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.89/3.39  tff(f_52, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 5.89/3.39  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.89/3.39  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.89/3.39  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.89/3.39  tff(f_95, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.89/3.39  tff(f_91, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 5.89/3.39  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.89/3.39  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.89/3.39  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 5.89/3.39  tff(c_44, plain, (![A_22]: (r2_hidden('#skF_3'(A_22), A_22) | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.89/3.39  tff(c_139, plain, (![D_65, A_66, B_67]: (r2_hidden(D_65, A_66) | ~r2_hidden(D_65, k4_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.89/3.39  tff(c_269, plain, (![A_100, B_101]: (r2_hidden('#skF_3'(k4_xboole_0(A_100, B_101)), A_100) | k4_xboole_0(A_100, B_101)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_139])).
% 5.89/3.39  tff(c_157, plain, (![D_70, B_71, A_72]: (~r2_hidden(D_70, B_71) | ~r2_hidden(D_70, k4_xboole_0(A_72, B_71)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.89/3.39  tff(c_165, plain, (![A_72, B_71]: (~r2_hidden('#skF_3'(k4_xboole_0(A_72, B_71)), B_71) | k4_xboole_0(A_72, B_71)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_157])).
% 5.89/3.39  tff(c_298, plain, (![A_100]: (k4_xboole_0(A_100, A_100)=k1_xboole_0)), inference(resolution, [status(thm)], [c_269, c_165])).
% 5.89/3.39  tff(c_22, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.89/3.39  tff(c_40, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.89/3.39  tff(c_62, plain, (k1_tops_1('#skF_4', k2_struct_0('#skF_4'))!=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.89/3.39  tff(c_28, plain, (![A_11]: (k1_subset_1(A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.89/3.39  tff(c_30, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.89/3.39  tff(c_34, plain, (![A_15]: (k3_subset_1(A_15, k1_subset_1(A_15))=k2_subset_1(A_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.89/3.39  tff(c_67, plain, (![A_15]: (k3_subset_1(A_15, k1_subset_1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34])).
% 5.89/3.39  tff(c_68, plain, (![A_15]: (k3_subset_1(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_67])).
% 5.89/3.39  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.89/3.39  tff(c_20, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.89/3.39  tff(c_36, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.89/3.39  tff(c_66, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.89/3.39  tff(c_54, plain, (![A_40]: (l1_struct_0(A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.89/3.39  tff(c_96, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.89/3.39  tff(c_102, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_54, c_96])).
% 5.89/3.39  tff(c_106, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_102])).
% 5.89/3.39  tff(c_472, plain, (![B_124, A_125]: (v4_pre_topc(B_124, A_125) | ~v1_xboole_0(B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.89/3.39  tff(c_487, plain, (![B_124]: (v4_pre_topc(B_124, '#skF_4') | ~v1_xboole_0(B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_472])).
% 5.89/3.39  tff(c_501, plain, (![B_127]: (v4_pre_topc(B_127, '#skF_4') | ~v1_xboole_0(B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_487])).
% 5.89/3.39  tff(c_517, plain, (v4_pre_topc(k1_xboole_0, '#skF_4') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_501])).
% 5.89/3.39  tff(c_523, plain, (v4_pre_topc(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_517])).
% 5.89/3.39  tff(c_593, plain, (![A_135, B_136]: (k2_pre_topc(A_135, B_136)=B_136 | ~v4_pre_topc(B_136, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.89/3.39  tff(c_619, plain, (![A_137]: (k2_pre_topc(A_137, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_137) | ~l1_pre_topc(A_137))), inference(resolution, [status(thm)], [c_36, c_593])).
% 5.89/3.39  tff(c_622, plain, (k2_pre_topc('#skF_4', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_523, c_619])).
% 5.89/3.39  tff(c_628, plain, (k2_pre_topc('#skF_4', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_622])).
% 5.89/3.39  tff(c_177, plain, (![A_76, B_77]: (k3_subset_1(A_76, k3_subset_1(A_76, B_77))=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.89/3.39  tff(c_181, plain, (![A_16]: (k3_subset_1(A_16, k3_subset_1(A_16, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_177])).
% 5.89/3.39  tff(c_184, plain, (![A_16]: (k3_subset_1(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_181])).
% 5.89/3.39  tff(c_1986, plain, (![A_234, B_235]: (k3_subset_1(u1_struct_0(A_234), k2_pre_topc(A_234, k3_subset_1(u1_struct_0(A_234), B_235)))=k1_tops_1(A_234, B_235) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_234))) | ~l1_pre_topc(A_234))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.89/3.39  tff(c_2016, plain, (![B_235]: (k3_subset_1(k2_struct_0('#skF_4'), k2_pre_topc('#skF_4', k3_subset_1(u1_struct_0('#skF_4'), B_235)))=k1_tops_1('#skF_4', B_235) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_1986])).
% 5.89/3.39  tff(c_2065, plain, (![B_237]: (k3_subset_1(k2_struct_0('#skF_4'), k2_pre_topc('#skF_4', k3_subset_1(k2_struct_0('#skF_4'), B_237)))=k1_tops_1('#skF_4', B_237) | ~m1_subset_1(B_237, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_106, c_106, c_2016])).
% 5.89/3.39  tff(c_2095, plain, (k3_subset_1(k2_struct_0('#skF_4'), k2_pre_topc('#skF_4', k1_xboole_0))=k1_tops_1('#skF_4', k2_struct_0('#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_184, c_2065])).
% 5.89/3.39  tff(c_2102, plain, (k1_tops_1('#skF_4', k2_struct_0('#skF_4'))=k2_struct_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_628, c_2095])).
% 5.89/3.39  tff(c_2103, plain, (~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_62, c_2102])).
% 5.89/3.39  tff(c_2109, plain, (~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_2103])).
% 5.89/3.39  tff(c_2112, plain, (k4_xboole_0(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_2109])).
% 5.89/3.39  tff(c_2116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_298, c_2112])).
% 5.89/3.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/3.39  
% 5.89/3.39  Inference rules
% 5.89/3.39  ----------------------
% 5.89/3.39  #Ref     : 0
% 5.89/3.39  #Sup     : 435
% 5.89/3.39  #Fact    : 0
% 5.89/3.39  #Define  : 0
% 5.89/3.39  #Split   : 2
% 5.89/3.39  #Chain   : 0
% 5.89/3.39  #Close   : 0
% 5.89/3.39  
% 5.89/3.39  Ordering : KBO
% 5.89/3.39  
% 5.89/3.39  Simplification rules
% 5.89/3.39  ----------------------
% 5.89/3.39  #Subsume      : 30
% 5.89/3.39  #Demod        : 168
% 5.89/3.39  #Tautology    : 146
% 5.89/3.39  #SimpNegUnit  : 3
% 5.89/3.39  #BackRed      : 0
% 5.89/3.39  
% 5.89/3.39  #Partial instantiations: 0
% 5.89/3.39  #Strategies tried      : 1
% 5.89/3.39  
% 5.89/3.39  Timing (in seconds)
% 5.89/3.39  ----------------------
% 5.89/3.41  Preprocessing        : 0.78
% 5.89/3.41  Parsing              : 0.42
% 5.89/3.41  CNF conversion       : 0.07
% 5.89/3.41  Main loop            : 1.47
% 5.89/3.41  Inferencing          : 0.55
% 5.89/3.41  Reduction            : 0.41
% 5.89/3.41  Demodulation         : 0.31
% 5.89/3.41  BG Simplification    : 0.09
% 5.89/3.41  Subsumption          : 0.29
% 5.89/3.41  Abstraction          : 0.10
% 5.89/3.41  MUC search           : 0.00
% 5.89/3.41  Cooper               : 0.00
% 5.89/3.41  Total                : 2.35
% 5.89/3.41  Index Insertion      : 0.00
% 5.89/3.41  Index Deletion       : 0.00
% 5.89/3.41  Index Matching       : 0.00
% 5.89/3.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
