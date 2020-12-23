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
% DateTime   : Thu Dec  3 10:31:02 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 155 expanded)
%              Number of leaves         :   35 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  154 ( 620 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v1_subset_1(B,u1_struct_0(A))
            <=> ~ r2_hidden(k3_yellow_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_94,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,C,D) )
                     => r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | B_2 = A_1
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34,plain,(
    v13_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_58,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_76,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_79,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_82,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_79])).

tff(c_52,plain,
    ( r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_83,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_52])).

tff(c_84,plain,(
    ! [B_49,A_50] :
      ( v1_subset_1(B_49,A_50)
      | B_49 = A_50
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_87,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32,c_84])).

tff(c_90,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_87])).

tff(c_40,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_59,plain,(
    ! [A_43] :
      ( k1_yellow_0(A_43,k1_xboole_0) = k3_yellow_0(A_43)
      | ~ l1_orders_2(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63,plain,(
    k1_yellow_0('#skF_4',k1_xboole_0) = k3_yellow_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_59])).

tff(c_70,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k1_yellow_0(A_47,B_48),u1_struct_0(A_47))
      | ~ l1_orders_2(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_73,plain,
    ( m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_70])).

tff(c_75,plain,(
    m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_73])).

tff(c_92,plain,(
    m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_75])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_92])).

tff(c_97,plain,(
    r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_44,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_42,plain,(
    v1_yellow_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_106,plain,(
    ! [A_53,C_54,B_55] :
      ( m1_subset_1(A_53,C_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_54))
      | ~ r2_hidden(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_109,plain,(
    ! [A_53] :
      ( m1_subset_1(A_53,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_53,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_106])).

tff(c_14,plain,(
    ! [A_12,B_14] :
      ( r1_orders_2(A_12,k3_yellow_0(A_12),B_14)
      | ~ m1_subset_1(B_14,u1_struct_0(A_12))
      | ~ l1_orders_2(A_12)
      | ~ v1_yellow_0(A_12)
      | ~ v5_orders_2(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_341,plain,(
    ! [D_115,B_116,A_117,C_118] :
      ( r2_hidden(D_115,B_116)
      | ~ r1_orders_2(A_117,C_118,D_115)
      | ~ r2_hidden(C_118,B_116)
      | ~ m1_subset_1(D_115,u1_struct_0(A_117))
      | ~ m1_subset_1(C_118,u1_struct_0(A_117))
      | ~ v13_waybel_0(B_116,A_117)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_orders_2(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_354,plain,(
    ! [B_123,B_124,A_125] :
      ( r2_hidden(B_123,B_124)
      | ~ r2_hidden(k3_yellow_0(A_125),B_124)
      | ~ m1_subset_1(k3_yellow_0(A_125),u1_struct_0(A_125))
      | ~ v13_waybel_0(B_124,A_125)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ m1_subset_1(B_123,u1_struct_0(A_125))
      | ~ l1_orders_2(A_125)
      | ~ v1_yellow_0(A_125)
      | ~ v5_orders_2(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_14,c_341])).

tff(c_357,plain,(
    ! [B_123,B_124] :
      ( r2_hidden(B_123,B_124)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_124)
      | ~ v13_waybel_0(B_124,'#skF_4')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v1_yellow_0('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_109,c_354])).

tff(c_362,plain,(
    ! [B_123,B_124] :
      ( r2_hidden(B_123,B_124)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_124)
      | ~ v13_waybel_0(B_124,'#skF_4')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_44,c_42,c_40,c_357])).

tff(c_368,plain,(
    ! [B_126,B_127] :
      ( r2_hidden(B_126,B_127)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_127)
      | ~ v13_waybel_0(B_127,'#skF_4')
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_126,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_362])).

tff(c_373,plain,(
    ! [B_126] :
      ( r2_hidden(B_126,'#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
      | ~ v13_waybel_0('#skF_5','#skF_4')
      | ~ m1_subset_1(B_126,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_32,c_368])).

tff(c_378,plain,(
    ! [B_128] :
      ( r2_hidden(B_128,'#skF_5')
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_97,c_373])).

tff(c_447,plain,(
    ! [B_132] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_132),'#skF_5')
      | u1_struct_0('#skF_4') = B_132
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_378])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | B_2 = A_1
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_455,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_447,c_2])).

tff(c_460,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_455])).

tff(c_96,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_482,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_96])).

tff(c_483,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_32])).

tff(c_30,plain,(
    ! [B_41] :
      ( ~ v1_subset_1(B_41,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_547,plain,(
    ~ v1_subset_1('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_483,c_30])).

tff(c_555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_547])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:25:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.46  
% 3.08/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.47  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 3.08/1.47  
% 3.08/1.47  %Foreground sorts:
% 3.08/1.47  
% 3.08/1.47  
% 3.08/1.47  %Background operators:
% 3.08/1.47  
% 3.08/1.47  
% 3.08/1.47  %Foreground operators:
% 3.08/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.08/1.47  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 3.08/1.47  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.47  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.08/1.47  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.08/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.47  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.08/1.47  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 3.08/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.08/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.08/1.47  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.08/1.47  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.08/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.47  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.08/1.47  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.08/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.08/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.08/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.08/1.47  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 3.08/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.47  
% 3.08/1.48  tff(f_123, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 3.08/1.48  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 3.08/1.48  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.08/1.48  tff(f_94, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 3.08/1.48  tff(f_50, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 3.08/1.48  tff(f_54, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 3.08/1.48  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.08/1.48  tff(f_68, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 3.08/1.48  tff(f_87, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 3.08/1.48  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.08/1.48  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | B_2=A_1 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.08/1.48  tff(c_34, plain, (v13_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.08/1.48  tff(c_38, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.08/1.48  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.08/1.48  tff(c_58, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.08/1.48  tff(c_76, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_58])).
% 3.08/1.48  tff(c_79, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_6, c_76])).
% 3.08/1.48  tff(c_82, plain, (~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_79])).
% 3.08/1.48  tff(c_52, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.08/1.48  tff(c_83, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_76, c_52])).
% 3.08/1.48  tff(c_84, plain, (![B_49, A_50]: (v1_subset_1(B_49, A_50) | B_49=A_50 | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.08/1.48  tff(c_87, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_32, c_84])).
% 3.08/1.48  tff(c_90, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_83, c_87])).
% 3.08/1.48  tff(c_40, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.08/1.48  tff(c_59, plain, (![A_43]: (k1_yellow_0(A_43, k1_xboole_0)=k3_yellow_0(A_43) | ~l1_orders_2(A_43))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.08/1.48  tff(c_63, plain, (k1_yellow_0('#skF_4', k1_xboole_0)=k3_yellow_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_59])).
% 3.08/1.48  tff(c_70, plain, (![A_47, B_48]: (m1_subset_1(k1_yellow_0(A_47, B_48), u1_struct_0(A_47)) | ~l1_orders_2(A_47))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.08/1.48  tff(c_73, plain, (m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_63, c_70])).
% 3.08/1.48  tff(c_75, plain, (m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_73])).
% 3.08/1.48  tff(c_92, plain, (m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_75])).
% 3.08/1.48  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_92])).
% 3.08/1.48  tff(c_97, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 3.08/1.48  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.08/1.48  tff(c_44, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.08/1.48  tff(c_42, plain, (v1_yellow_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.08/1.48  tff(c_106, plain, (![A_53, C_54, B_55]: (m1_subset_1(A_53, C_54) | ~m1_subset_1(B_55, k1_zfmisc_1(C_54)) | ~r2_hidden(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.08/1.48  tff(c_109, plain, (![A_53]: (m1_subset_1(A_53, u1_struct_0('#skF_4')) | ~r2_hidden(A_53, '#skF_5'))), inference(resolution, [status(thm)], [c_32, c_106])).
% 3.08/1.48  tff(c_14, plain, (![A_12, B_14]: (r1_orders_2(A_12, k3_yellow_0(A_12), B_14) | ~m1_subset_1(B_14, u1_struct_0(A_12)) | ~l1_orders_2(A_12) | ~v1_yellow_0(A_12) | ~v5_orders_2(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.08/1.48  tff(c_341, plain, (![D_115, B_116, A_117, C_118]: (r2_hidden(D_115, B_116) | ~r1_orders_2(A_117, C_118, D_115) | ~r2_hidden(C_118, B_116) | ~m1_subset_1(D_115, u1_struct_0(A_117)) | ~m1_subset_1(C_118, u1_struct_0(A_117)) | ~v13_waybel_0(B_116, A_117) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_orders_2(A_117))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.08/1.48  tff(c_354, plain, (![B_123, B_124, A_125]: (r2_hidden(B_123, B_124) | ~r2_hidden(k3_yellow_0(A_125), B_124) | ~m1_subset_1(k3_yellow_0(A_125), u1_struct_0(A_125)) | ~v13_waybel_0(B_124, A_125) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_125))) | ~m1_subset_1(B_123, u1_struct_0(A_125)) | ~l1_orders_2(A_125) | ~v1_yellow_0(A_125) | ~v5_orders_2(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_14, c_341])).
% 3.08/1.48  tff(c_357, plain, (![B_123, B_124]: (r2_hidden(B_123, B_124) | ~r2_hidden(k3_yellow_0('#skF_4'), B_124) | ~v13_waybel_0(B_124, '#skF_4') | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_123, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v1_yellow_0('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_109, c_354])).
% 3.08/1.48  tff(c_362, plain, (![B_123, B_124]: (r2_hidden(B_123, B_124) | ~r2_hidden(k3_yellow_0('#skF_4'), B_124) | ~v13_waybel_0(B_124, '#skF_4') | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_123, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_44, c_42, c_40, c_357])).
% 3.08/1.48  tff(c_368, plain, (![B_126, B_127]: (r2_hidden(B_126, B_127) | ~r2_hidden(k3_yellow_0('#skF_4'), B_127) | ~v13_waybel_0(B_127, '#skF_4') | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_126, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_50, c_362])).
% 3.08/1.48  tff(c_373, plain, (![B_126]: (r2_hidden(B_126, '#skF_5') | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v13_waybel_0('#skF_5', '#skF_4') | ~m1_subset_1(B_126, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_32, c_368])).
% 3.08/1.48  tff(c_378, plain, (![B_128]: (r2_hidden(B_128, '#skF_5') | ~m1_subset_1(B_128, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_97, c_373])).
% 3.08/1.48  tff(c_447, plain, (![B_132]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_132), '#skF_5') | u1_struct_0('#skF_4')=B_132 | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_4, c_378])).
% 3.08/1.48  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | B_2=A_1 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.08/1.48  tff(c_455, plain, (u1_struct_0('#skF_4')='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_447, c_2])).
% 3.08/1.48  tff(c_460, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_455])).
% 3.08/1.48  tff(c_96, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_58])).
% 3.08/1.48  tff(c_482, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_460, c_96])).
% 3.08/1.48  tff(c_483, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_460, c_32])).
% 3.08/1.48  tff(c_30, plain, (![B_41]: (~v1_subset_1(B_41, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.08/1.48  tff(c_547, plain, (~v1_subset_1('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_483, c_30])).
% 3.08/1.48  tff(c_555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_482, c_547])).
% 3.08/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.48  
% 3.08/1.48  Inference rules
% 3.08/1.48  ----------------------
% 3.08/1.48  #Ref     : 0
% 3.08/1.48  #Sup     : 84
% 3.08/1.48  #Fact    : 0
% 3.08/1.48  #Define  : 0
% 3.08/1.48  #Split   : 3
% 3.08/1.48  #Chain   : 0
% 3.08/1.48  #Close   : 0
% 3.08/1.48  
% 3.08/1.48  Ordering : KBO
% 3.08/1.48  
% 3.08/1.48  Simplification rules
% 3.08/1.48  ----------------------
% 3.08/1.48  #Subsume      : 3
% 3.08/1.48  #Demod        : 120
% 3.08/1.48  #Tautology    : 23
% 3.08/1.48  #SimpNegUnit  : 12
% 3.08/1.48  #BackRed      : 26
% 3.08/1.48  
% 3.08/1.48  #Partial instantiations: 0
% 3.08/1.48  #Strategies tried      : 1
% 3.08/1.48  
% 3.08/1.48  Timing (in seconds)
% 3.08/1.48  ----------------------
% 3.08/1.49  Preprocessing        : 0.34
% 3.08/1.49  Parsing              : 0.19
% 3.08/1.49  CNF conversion       : 0.02
% 3.08/1.49  Main loop            : 0.34
% 3.08/1.49  Inferencing          : 0.13
% 3.08/1.49  Reduction            : 0.10
% 3.08/1.49  Demodulation         : 0.07
% 3.08/1.49  BG Simplification    : 0.02
% 3.08/1.49  Subsumption          : 0.06
% 3.08/1.49  Abstraction          : 0.02
% 3.08/1.49  MUC search           : 0.00
% 3.08/1.49  Cooper               : 0.00
% 3.08/1.49  Total                : 0.72
% 3.08/1.49  Index Insertion      : 0.00
% 3.08/1.49  Index Deletion       : 0.00
% 3.08/1.49  Index Matching       : 0.00
% 3.08/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
