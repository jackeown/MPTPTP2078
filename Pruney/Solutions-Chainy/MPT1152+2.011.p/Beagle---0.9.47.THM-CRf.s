%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:29 EST 2020

% Result     : Theorem 5.51s
% Output     : CNFRefutation 5.76s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 785 expanded)
%              Number of leaves         :   39 ( 294 expanded)
%              Depth                    :   18
%              Number of atoms          :  245 (2165 expanded)
%              Number of equality atoms :   35 ( 448 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_164,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_104,axiom,(
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

tff(f_69,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_150,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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

tff(f_88,axiom,(
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

tff(f_119,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

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
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_50,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_48,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_46,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_44,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_28,plain,(
    ! [A_46] :
      ( l1_struct_0(A_46)
      | ~ l1_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_66,plain,(
    ! [A_64] :
      ( u1_struct_0(A_64) = k2_struct_0(A_64)
      | ~ l1_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_71,plain,(
    ! [A_65] :
      ( u1_struct_0(A_65) = k2_struct_0(A_65)
      | ~ l1_orders_2(A_65) ) ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_75,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_351,plain,(
    ! [A_106,B_107] :
      ( k2_orders_2(A_106,B_107) = a_2_1_orders_2(A_106,B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_orders_2(A_106)
      | ~ v5_orders_2(A_106)
      | ~ v4_orders_2(A_106)
      | ~ v3_orders_2(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_366,plain,(
    ! [B_107] :
      ( k2_orders_2('#skF_4',B_107) = a_2_1_orders_2('#skF_4',B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_351])).

tff(c_375,plain,(
    ! [B_107] :
      ( k2_orders_2('#skF_4',B_107) = a_2_1_orders_2('#skF_4',B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_366])).

tff(c_378,plain,(
    ! [B_108] :
      ( k2_orders_2('#skF_4',B_108) = a_2_1_orders_2('#skF_4',B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_375])).

tff(c_398,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_53,c_378])).

tff(c_42,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_399,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_42])).

tff(c_14,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_1'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_640,plain,(
    ! [A_125,B_126,C_127] :
      ( m1_subset_1('#skF_2'(A_125,B_126,C_127),u1_struct_0(B_126))
      | ~ r2_hidden(A_125,a_2_1_orders_2(B_126,C_127))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(B_126)))
      | ~ l1_orders_2(B_126)
      | ~ v5_orders_2(B_126)
      | ~ v4_orders_2(B_126)
      | ~ v3_orders_2(B_126)
      | v2_struct_0(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_645,plain,(
    ! [A_125,C_127] :
      ( m1_subset_1('#skF_2'(A_125,'#skF_4',C_127),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_125,a_2_1_orders_2('#skF_4',C_127))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_640])).

tff(c_648,plain,(
    ! [A_125,C_127] :
      ( m1_subset_1('#skF_2'(A_125,'#skF_4',C_127),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_125,a_2_1_orders_2('#skF_4',C_127))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_75,c_645])).

tff(c_649,plain,(
    ! [A_125,C_127] :
      ( m1_subset_1('#skF_2'(A_125,'#skF_4',C_127),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_125,a_2_1_orders_2('#skF_4',C_127))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_648])).

tff(c_96,plain,(
    ! [A_76,C_77,B_78] :
      ( m1_subset_1(A_76,C_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(C_77))
      | ~ r2_hidden(A_76,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_101,plain,(
    ! [A_82,A_83] :
      ( m1_subset_1(A_82,A_83)
      | ~ r2_hidden(A_82,A_83) ) ),
    inference(resolution,[status(thm)],[c_53,c_96])).

tff(c_110,plain,(
    ! [A_84] :
      ( m1_subset_1('#skF_1'(A_84),A_84)
      | k1_xboole_0 = A_84 ) ),
    inference(resolution,[status(thm)],[c_14,c_101])).

tff(c_10,plain,(
    ! [C_10,B_9,A_8] :
      ( ~ v1_xboole_0(C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_119,plain,(
    ! [C_85,A_86] :
      ( ~ v1_xboole_0(C_85)
      | ~ r2_hidden(A_86,'#skF_1'(k1_zfmisc_1(C_85)))
      | k1_zfmisc_1(C_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_110,c_10])).

tff(c_130,plain,(
    ! [C_87] :
      ( ~ v1_xboole_0(C_87)
      | k1_zfmisc_1(C_87) = k1_xboole_0
      | '#skF_1'(k1_zfmisc_1(C_87)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_119])).

tff(c_109,plain,(
    ! [A_11] :
      ( m1_subset_1('#skF_1'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_14,c_101])).

tff(c_139,plain,(
    ! [C_87] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(C_87))
      | k1_zfmisc_1(C_87) = k1_xboole_0
      | ~ v1_xboole_0(C_87)
      | k1_zfmisc_1(C_87) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_109])).

tff(c_396,plain,
    ( k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0)
    | ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | k1_zfmisc_1(k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_139,c_378])).

tff(c_404,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_396])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1066,plain,(
    ! [B_149,A_150,C_151,E_152] :
      ( r2_orders_2(B_149,'#skF_2'(A_150,B_149,C_151),E_152)
      | ~ r2_hidden(E_152,C_151)
      | ~ m1_subset_1(E_152,u1_struct_0(B_149))
      | ~ r2_hidden(A_150,a_2_1_orders_2(B_149,C_151))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(u1_struct_0(B_149)))
      | ~ l1_orders_2(B_149)
      | ~ v5_orders_2(B_149)
      | ~ v4_orders_2(B_149)
      | ~ v3_orders_2(B_149)
      | v2_struct_0(B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2510,plain,(
    ! [B_213,A_214,E_215] :
      ( r2_orders_2(B_213,'#skF_2'(A_214,B_213,u1_struct_0(B_213)),E_215)
      | ~ r2_hidden(E_215,u1_struct_0(B_213))
      | ~ m1_subset_1(E_215,u1_struct_0(B_213))
      | ~ r2_hidden(A_214,a_2_1_orders_2(B_213,u1_struct_0(B_213)))
      | ~ l1_orders_2(B_213)
      | ~ v5_orders_2(B_213)
      | ~ v4_orders_2(B_213)
      | ~ v3_orders_2(B_213)
      | v2_struct_0(B_213) ) ),
    inference(resolution,[status(thm)],[c_53,c_1066])).

tff(c_2521,plain,(
    ! [A_214,E_215] :
      ( r2_orders_2('#skF_4','#skF_2'(A_214,'#skF_4',k2_struct_0('#skF_4')),E_215)
      | ~ r2_hidden(E_215,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_215,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_214,a_2_1_orders_2('#skF_4',u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_2510])).

tff(c_2526,plain,(
    ! [A_214,E_215] :
      ( r2_orders_2('#skF_4','#skF_2'(A_214,'#skF_4',k2_struct_0('#skF_4')),E_215)
      | ~ r2_hidden(E_215,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_215,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_214,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_75,c_75,c_75,c_2521])).

tff(c_2571,plain,(
    ! [A_217,E_218] :
      ( r2_orders_2('#skF_4','#skF_2'(A_217,'#skF_4',k2_struct_0('#skF_4')),E_218)
      | ~ r2_hidden(E_218,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_218,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_217,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2526])).

tff(c_20,plain,(
    ! [A_34,C_40] :
      ( ~ r2_orders_2(A_34,C_40,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2579,plain,(
    ! [A_217] :
      ( ~ m1_subset_1('#skF_2'(A_217,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_217,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_217,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_217,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2571,c_20])).

tff(c_3071,plain,(
    ! [A_241] :
      ( ~ r2_hidden('#skF_2'(A_241,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_241,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_241,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_75,c_2579])).

tff(c_3080,plain,(
    ! [A_241] :
      ( ~ r2_hidden(A_241,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_241,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_3071])).

tff(c_3086,plain,(
    ! [A_242] :
      ( ~ r2_hidden(A_242,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_242,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_3080])).

tff(c_3096,plain,(
    ! [A_125] :
      ( ~ r2_hidden(A_125,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_649,c_3086])).

tff(c_3133,plain,(
    ! [A_247] : ~ r2_hidden(A_247,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_3096])).

tff(c_3141,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_3133])).

tff(c_3148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_399,c_3141])).

tff(c_3150,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_396])).

tff(c_81,plain,(
    ! [C_68,B_69,A_70] :
      ( ~ v1_xboole_0(C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_86,plain,(
    ! [A_73,A_74] :
      ( ~ v1_xboole_0(A_73)
      | ~ r2_hidden(A_74,A_73) ) ),
    inference(resolution,[status(thm)],[c_53,c_81])).

tff(c_94,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_14,c_86])).

tff(c_3154,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3150,c_94])).

tff(c_3156,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3154,c_399])).

tff(c_3155,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3154,c_3150])).

tff(c_3160,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3154,c_75])).

tff(c_3157,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3154,c_3154,c_398])).

tff(c_3217,plain,(
    ! [A_249,B_250] :
      ( m1_subset_1(k2_orders_2(A_249,B_250),k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_orders_2(A_249)
      | ~ v5_orders_2(A_249)
      | ~ v4_orders_2(A_249)
      | ~ v3_orders_2(A_249)
      | v2_struct_0(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_3227,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3157,c_3217])).

tff(c_3235,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_53,c_3160,c_3160,c_3227])).

tff(c_3236,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3235])).

tff(c_3246,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_8,a_2_1_orders_2('#skF_4',k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_3236,c_10])).

tff(c_3254,plain,(
    ! [A_251] : ~ r2_hidden(A_251,a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3155,c_3246])).

tff(c_3262,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_3254])).

tff(c_3267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3156,c_3262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.51/2.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.18  
% 5.76/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.18  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 5.76/2.18  
% 5.76/2.18  %Foreground sorts:
% 5.76/2.18  
% 5.76/2.18  
% 5.76/2.18  %Background operators:
% 5.76/2.18  
% 5.76/2.18  
% 5.76/2.18  %Foreground operators:
% 5.76/2.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.76/2.18  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.76/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.76/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.76/2.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.76/2.18  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.76/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.76/2.18  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 5.76/2.18  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 5.76/2.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.76/2.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.76/2.18  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.76/2.18  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.76/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.76/2.18  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.76/2.18  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.76/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.76/2.18  tff('#skF_4', type, '#skF_4': $i).
% 5.76/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.76/2.18  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 5.76/2.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.76/2.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.76/2.18  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.76/2.18  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.76/2.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.76/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.76/2.18  
% 5.76/2.20  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.76/2.20  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.76/2.20  tff(f_164, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_orders_2)).
% 5.76/2.20  tff(f_123, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 5.76/2.20  tff(f_73, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.76/2.20  tff(f_104, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 5.76/2.20  tff(f_69, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 5.76/2.20  tff(f_150, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 5.76/2.20  tff(f_41, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.76/2.20  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.76/2.20  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.76/2.20  tff(f_88, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 5.76/2.20  tff(f_119, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 5.76/2.20  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.76/2.20  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.76/2.20  tff(c_53, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 5.76/2.20  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.76/2.20  tff(c_50, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.76/2.20  tff(c_48, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.76/2.20  tff(c_46, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.76/2.20  tff(c_44, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.76/2.20  tff(c_28, plain, (![A_46]: (l1_struct_0(A_46) | ~l1_orders_2(A_46))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.76/2.20  tff(c_66, plain, (![A_64]: (u1_struct_0(A_64)=k2_struct_0(A_64) | ~l1_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.76/2.20  tff(c_71, plain, (![A_65]: (u1_struct_0(A_65)=k2_struct_0(A_65) | ~l1_orders_2(A_65))), inference(resolution, [status(thm)], [c_28, c_66])).
% 5.76/2.20  tff(c_75, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_71])).
% 5.76/2.20  tff(c_351, plain, (![A_106, B_107]: (k2_orders_2(A_106, B_107)=a_2_1_orders_2(A_106, B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_orders_2(A_106) | ~v5_orders_2(A_106) | ~v4_orders_2(A_106) | ~v3_orders_2(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.76/2.20  tff(c_366, plain, (![B_107]: (k2_orders_2('#skF_4', B_107)=a_2_1_orders_2('#skF_4', B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_351])).
% 5.76/2.20  tff(c_375, plain, (![B_107]: (k2_orders_2('#skF_4', B_107)=a_2_1_orders_2('#skF_4', B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_366])).
% 5.76/2.20  tff(c_378, plain, (![B_108]: (k2_orders_2('#skF_4', B_108)=a_2_1_orders_2('#skF_4', B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_375])).
% 5.76/2.20  tff(c_398, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_53, c_378])).
% 5.76/2.20  tff(c_42, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.76/2.20  tff(c_399, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_398, c_42])).
% 5.76/2.20  tff(c_14, plain, (![A_11]: (r2_hidden('#skF_1'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.76/2.20  tff(c_640, plain, (![A_125, B_126, C_127]: (m1_subset_1('#skF_2'(A_125, B_126, C_127), u1_struct_0(B_126)) | ~r2_hidden(A_125, a_2_1_orders_2(B_126, C_127)) | ~m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(B_126))) | ~l1_orders_2(B_126) | ~v5_orders_2(B_126) | ~v4_orders_2(B_126) | ~v3_orders_2(B_126) | v2_struct_0(B_126))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.76/2.20  tff(c_645, plain, (![A_125, C_127]: (m1_subset_1('#skF_2'(A_125, '#skF_4', C_127), k2_struct_0('#skF_4')) | ~r2_hidden(A_125, a_2_1_orders_2('#skF_4', C_127)) | ~m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_640])).
% 5.76/2.20  tff(c_648, plain, (![A_125, C_127]: (m1_subset_1('#skF_2'(A_125, '#skF_4', C_127), k2_struct_0('#skF_4')) | ~r2_hidden(A_125, a_2_1_orders_2('#skF_4', C_127)) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_75, c_645])).
% 5.76/2.20  tff(c_649, plain, (![A_125, C_127]: (m1_subset_1('#skF_2'(A_125, '#skF_4', C_127), k2_struct_0('#skF_4')) | ~r2_hidden(A_125, a_2_1_orders_2('#skF_4', C_127)) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_648])).
% 5.76/2.20  tff(c_96, plain, (![A_76, C_77, B_78]: (m1_subset_1(A_76, C_77) | ~m1_subset_1(B_78, k1_zfmisc_1(C_77)) | ~r2_hidden(A_76, B_78))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.76/2.20  tff(c_101, plain, (![A_82, A_83]: (m1_subset_1(A_82, A_83) | ~r2_hidden(A_82, A_83))), inference(resolution, [status(thm)], [c_53, c_96])).
% 5.76/2.20  tff(c_110, plain, (![A_84]: (m1_subset_1('#skF_1'(A_84), A_84) | k1_xboole_0=A_84)), inference(resolution, [status(thm)], [c_14, c_101])).
% 5.76/2.20  tff(c_10, plain, (![C_10, B_9, A_8]: (~v1_xboole_0(C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.76/2.20  tff(c_119, plain, (![C_85, A_86]: (~v1_xboole_0(C_85) | ~r2_hidden(A_86, '#skF_1'(k1_zfmisc_1(C_85))) | k1_zfmisc_1(C_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_10])).
% 5.76/2.20  tff(c_130, plain, (![C_87]: (~v1_xboole_0(C_87) | k1_zfmisc_1(C_87)=k1_xboole_0 | '#skF_1'(k1_zfmisc_1(C_87))=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_119])).
% 5.76/2.20  tff(c_109, plain, (![A_11]: (m1_subset_1('#skF_1'(A_11), A_11) | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_14, c_101])).
% 5.76/2.20  tff(c_139, plain, (![C_87]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(C_87)) | k1_zfmisc_1(C_87)=k1_xboole_0 | ~v1_xboole_0(C_87) | k1_zfmisc_1(C_87)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_130, c_109])).
% 5.76/2.20  tff(c_396, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0) | ~v1_xboole_0(k2_struct_0('#skF_4')) | k1_zfmisc_1(k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_139, c_378])).
% 5.76/2.20  tff(c_404, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_396])).
% 5.76/2.20  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.76/2.20  tff(c_1066, plain, (![B_149, A_150, C_151, E_152]: (r2_orders_2(B_149, '#skF_2'(A_150, B_149, C_151), E_152) | ~r2_hidden(E_152, C_151) | ~m1_subset_1(E_152, u1_struct_0(B_149)) | ~r2_hidden(A_150, a_2_1_orders_2(B_149, C_151)) | ~m1_subset_1(C_151, k1_zfmisc_1(u1_struct_0(B_149))) | ~l1_orders_2(B_149) | ~v5_orders_2(B_149) | ~v4_orders_2(B_149) | ~v3_orders_2(B_149) | v2_struct_0(B_149))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.76/2.20  tff(c_2510, plain, (![B_213, A_214, E_215]: (r2_orders_2(B_213, '#skF_2'(A_214, B_213, u1_struct_0(B_213)), E_215) | ~r2_hidden(E_215, u1_struct_0(B_213)) | ~m1_subset_1(E_215, u1_struct_0(B_213)) | ~r2_hidden(A_214, a_2_1_orders_2(B_213, u1_struct_0(B_213))) | ~l1_orders_2(B_213) | ~v5_orders_2(B_213) | ~v4_orders_2(B_213) | ~v3_orders_2(B_213) | v2_struct_0(B_213))), inference(resolution, [status(thm)], [c_53, c_1066])).
% 5.76/2.20  tff(c_2521, plain, (![A_214, E_215]: (r2_orders_2('#skF_4', '#skF_2'(A_214, '#skF_4', k2_struct_0('#skF_4')), E_215) | ~r2_hidden(E_215, u1_struct_0('#skF_4')) | ~m1_subset_1(E_215, u1_struct_0('#skF_4')) | ~r2_hidden(A_214, a_2_1_orders_2('#skF_4', u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_2510])).
% 5.76/2.20  tff(c_2526, plain, (![A_214, E_215]: (r2_orders_2('#skF_4', '#skF_2'(A_214, '#skF_4', k2_struct_0('#skF_4')), E_215) | ~r2_hidden(E_215, k2_struct_0('#skF_4')) | ~m1_subset_1(E_215, k2_struct_0('#skF_4')) | ~r2_hidden(A_214, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_75, c_75, c_75, c_2521])).
% 5.76/2.20  tff(c_2571, plain, (![A_217, E_218]: (r2_orders_2('#skF_4', '#skF_2'(A_217, '#skF_4', k2_struct_0('#skF_4')), E_218) | ~r2_hidden(E_218, k2_struct_0('#skF_4')) | ~m1_subset_1(E_218, k2_struct_0('#skF_4')) | ~r2_hidden(A_217, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_2526])).
% 5.76/2.20  tff(c_20, plain, (![A_34, C_40]: (~r2_orders_2(A_34, C_40, C_40) | ~m1_subset_1(C_40, u1_struct_0(A_34)) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.76/2.20  tff(c_2579, plain, (![A_217]: (~m1_subset_1('#skF_2'(A_217, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_217, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_217, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_217, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2571, c_20])).
% 5.76/2.20  tff(c_3071, plain, (![A_241]: (~r2_hidden('#skF_2'(A_241, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_241, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_241, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_75, c_2579])).
% 5.76/2.20  tff(c_3080, plain, (![A_241]: (~r2_hidden(A_241, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_241, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_3071])).
% 5.76/2.20  tff(c_3086, plain, (![A_242]: (~r2_hidden(A_242, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_242, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_404, c_3080])).
% 5.76/2.20  tff(c_3096, plain, (![A_125]: (~r2_hidden(A_125, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_649, c_3086])).
% 5.76/2.20  tff(c_3133, plain, (![A_247]: (~r2_hidden(A_247, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_3096])).
% 5.76/2.20  tff(c_3141, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_3133])).
% 5.76/2.20  tff(c_3148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_399, c_3141])).
% 5.76/2.20  tff(c_3150, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_396])).
% 5.76/2.20  tff(c_81, plain, (![C_68, B_69, A_70]: (~v1_xboole_0(C_68) | ~m1_subset_1(B_69, k1_zfmisc_1(C_68)) | ~r2_hidden(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.76/2.20  tff(c_86, plain, (![A_73, A_74]: (~v1_xboole_0(A_73) | ~r2_hidden(A_74, A_73))), inference(resolution, [status(thm)], [c_53, c_81])).
% 5.76/2.20  tff(c_94, plain, (![A_11]: (~v1_xboole_0(A_11) | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_14, c_86])).
% 5.76/2.20  tff(c_3154, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_3150, c_94])).
% 5.76/2.20  tff(c_3156, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3154, c_399])).
% 5.76/2.20  tff(c_3155, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3154, c_3150])).
% 5.76/2.20  tff(c_3160, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3154, c_75])).
% 5.76/2.20  tff(c_3157, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3154, c_3154, c_398])).
% 5.76/2.20  tff(c_3217, plain, (![A_249, B_250]: (m1_subset_1(k2_orders_2(A_249, B_250), k1_zfmisc_1(u1_struct_0(A_249))) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_orders_2(A_249) | ~v5_orders_2(A_249) | ~v4_orders_2(A_249) | ~v3_orders_2(A_249) | v2_struct_0(A_249))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.76/2.20  tff(c_3227, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3157, c_3217])).
% 5.76/2.20  tff(c_3235, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_53, c_3160, c_3160, c_3227])).
% 5.76/2.20  tff(c_3236, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_52, c_3235])).
% 5.76/2.20  tff(c_3246, plain, (![A_8]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_8, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(resolution, [status(thm)], [c_3236, c_10])).
% 5.76/2.20  tff(c_3254, plain, (![A_251]: (~r2_hidden(A_251, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_3155, c_3246])).
% 5.76/2.20  tff(c_3262, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_3254])).
% 5.76/2.20  tff(c_3267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3156, c_3262])).
% 5.76/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.20  
% 5.76/2.20  Inference rules
% 5.76/2.20  ----------------------
% 5.76/2.20  #Ref     : 0
% 5.76/2.20  #Sup     : 684
% 5.76/2.20  #Fact    : 0
% 5.76/2.20  #Define  : 0
% 5.76/2.20  #Split   : 19
% 5.76/2.20  #Chain   : 0
% 5.76/2.20  #Close   : 0
% 5.76/2.20  
% 5.76/2.20  Ordering : KBO
% 5.76/2.20  
% 5.76/2.20  Simplification rules
% 5.76/2.20  ----------------------
% 5.76/2.20  #Subsume      : 217
% 5.76/2.20  #Demod        : 1196
% 5.76/2.20  #Tautology    : 206
% 5.76/2.20  #SimpNegUnit  : 206
% 5.76/2.20  #BackRed      : 129
% 5.76/2.20  
% 5.76/2.20  #Partial instantiations: 0
% 5.76/2.20  #Strategies tried      : 1
% 5.76/2.20  
% 5.76/2.20  Timing (in seconds)
% 5.76/2.20  ----------------------
% 5.76/2.20  Preprocessing        : 0.41
% 5.76/2.20  Parsing              : 0.18
% 5.76/2.20  CNF conversion       : 0.03
% 5.76/2.20  Main loop            : 0.99
% 5.76/2.20  Inferencing          : 0.31
% 5.76/2.20  Reduction            : 0.36
% 5.76/2.20  Demodulation         : 0.25
% 5.76/2.21  BG Simplification    : 0.04
% 5.76/2.21  Subsumption          : 0.21
% 5.76/2.21  Abstraction          : 0.06
% 5.76/2.21  MUC search           : 0.00
% 5.76/2.21  Cooper               : 0.00
% 5.76/2.21  Total                : 1.45
% 5.76/2.21  Index Insertion      : 0.00
% 5.76/2.21  Index Deletion       : 0.00
% 5.76/2.21  Index Matching       : 0.00
% 5.76/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
