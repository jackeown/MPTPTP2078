%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:05 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 147 expanded)
%              Number of leaves         :   32 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 601 expanded)
%              Number of equality atoms :   10 (  19 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

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

tff(f_119,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_83,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | B_2 = A_1
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    v13_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_50,plain,
    ( r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_59,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_61,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_56])).

tff(c_64,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_61])).

tff(c_67,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_64])).

tff(c_38,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_68,plain,(
    ! [B_45,A_46] :
      ( v1_subset_1(B_45,A_46)
      | B_45 = A_46
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_71,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_30,c_68])).

tff(c_74,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_71])).

tff(c_10,plain,(
    ! [A_9] :
      ( m1_subset_1(k3_yellow_0(A_9),u1_struct_0(A_9))
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_80,plain,
    ( m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_10])).

tff(c_84,plain,(
    m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_80])).

tff(c_86,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_84])).

tff(c_87,plain,(
    r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_42,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_40,plain,(
    v1_yellow_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_103,plain,(
    ! [A_51,C_52,B_53] :
      ( m1_subset_1(A_51,C_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(C_52))
      | ~ r2_hidden(A_51,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_106,plain,(
    ! [A_51] :
      ( m1_subset_1(A_51,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_51,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_103])).

tff(c_12,plain,(
    ! [A_10,B_12] :
      ( r1_orders_2(A_10,k3_yellow_0(A_10),B_12)
      | ~ m1_subset_1(B_12,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10)
      | ~ v1_yellow_0(A_10)
      | ~ v5_orders_2(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_319,plain,(
    ! [D_110,B_111,A_112,C_113] :
      ( r2_hidden(D_110,B_111)
      | ~ r1_orders_2(A_112,C_113,D_110)
      | ~ r2_hidden(C_113,B_111)
      | ~ m1_subset_1(D_110,u1_struct_0(A_112))
      | ~ m1_subset_1(C_113,u1_struct_0(A_112))
      | ~ v13_waybel_0(B_111,A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_orders_2(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_332,plain,(
    ! [B_118,B_119,A_120] :
      ( r2_hidden(B_118,B_119)
      | ~ r2_hidden(k3_yellow_0(A_120),B_119)
      | ~ m1_subset_1(k3_yellow_0(A_120),u1_struct_0(A_120))
      | ~ v13_waybel_0(B_119,A_120)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(B_118,u1_struct_0(A_120))
      | ~ l1_orders_2(A_120)
      | ~ v1_yellow_0(A_120)
      | ~ v5_orders_2(A_120)
      | v2_struct_0(A_120) ) ),
    inference(resolution,[status(thm)],[c_12,c_319])).

tff(c_335,plain,(
    ! [B_118,B_119] :
      ( r2_hidden(B_118,B_119)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_119)
      | ~ v13_waybel_0(B_119,'#skF_4')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_118,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v1_yellow_0('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_106,c_332])).

tff(c_340,plain,(
    ! [B_118,B_119] :
      ( r2_hidden(B_118,B_119)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_119)
      | ~ v13_waybel_0(B_119,'#skF_4')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_118,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_42,c_40,c_38,c_335])).

tff(c_343,plain,(
    ! [B_121,B_122] :
      ( r2_hidden(B_121,B_122)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_122)
      | ~ v13_waybel_0(B_122,'#skF_4')
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_340])).

tff(c_348,plain,(
    ! [B_121] :
      ( r2_hidden(B_121,'#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
      | ~ v13_waybel_0('#skF_5','#skF_4')
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_30,c_343])).

tff(c_353,plain,(
    ! [B_123] :
      ( r2_hidden(B_123,'#skF_5')
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_87,c_348])).

tff(c_413,plain,(
    ! [B_126] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_126),'#skF_5')
      | u1_struct_0('#skF_4') = B_126
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_353])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | B_2 = A_1
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_421,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_413,c_2])).

tff(c_426,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_421])).

tff(c_88,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_437,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_88])).

tff(c_438,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_30])).

tff(c_28,plain,(
    ! [B_39] :
      ( ~ v1_subset_1(B_39,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_506,plain,(
    ~ v1_subset_1('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_438,c_28])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_506])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:11:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.38  
% 2.91/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.39  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.91/1.39  
% 2.91/1.39  %Foreground sorts:
% 2.91/1.39  
% 2.91/1.39  
% 2.91/1.39  %Background operators:
% 2.91/1.39  
% 2.91/1.39  
% 2.91/1.39  %Foreground operators:
% 2.91/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.91/1.39  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.91/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.39  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.91/1.39  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.91/1.39  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.91/1.39  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 2.91/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.91/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.39  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.91/1.39  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.91/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.39  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.91/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.91/1.39  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.91/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.91/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.91/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.91/1.39  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 2.91/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.39  
% 2.91/1.40  tff(f_119, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 2.91/1.40  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 2.91/1.40  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.91/1.40  tff(f_90, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.91/1.40  tff(f_50, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 2.91/1.40  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.91/1.40  tff(f_64, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_yellow_0)).
% 2.91/1.40  tff(f_83, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 2.91/1.40  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.40  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | B_2=A_1 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.91/1.40  tff(c_32, plain, (v13_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.40  tff(c_36, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.40  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.91/1.40  tff(c_50, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.40  tff(c_59, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_50])).
% 2.91/1.40  tff(c_56, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.40  tff(c_61, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_59, c_56])).
% 2.91/1.40  tff(c_64, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_6, c_61])).
% 2.91/1.40  tff(c_67, plain, (~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_36, c_64])).
% 2.91/1.40  tff(c_38, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.40  tff(c_68, plain, (![B_45, A_46]: (v1_subset_1(B_45, A_46) | B_45=A_46 | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.91/1.40  tff(c_71, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_30, c_68])).
% 2.91/1.40  tff(c_74, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_59, c_71])).
% 2.91/1.40  tff(c_10, plain, (![A_9]: (m1_subset_1(k3_yellow_0(A_9), u1_struct_0(A_9)) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.91/1.40  tff(c_80, plain, (m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5') | ~l1_orders_2('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_74, c_10])).
% 2.91/1.40  tff(c_84, plain, (m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_80])).
% 2.91/1.40  tff(c_86, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_84])).
% 2.91/1.40  tff(c_87, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 2.91/1.40  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.40  tff(c_42, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.40  tff(c_40, plain, (v1_yellow_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.40  tff(c_103, plain, (![A_51, C_52, B_53]: (m1_subset_1(A_51, C_52) | ~m1_subset_1(B_53, k1_zfmisc_1(C_52)) | ~r2_hidden(A_51, B_53))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.91/1.40  tff(c_106, plain, (![A_51]: (m1_subset_1(A_51, u1_struct_0('#skF_4')) | ~r2_hidden(A_51, '#skF_5'))), inference(resolution, [status(thm)], [c_30, c_103])).
% 2.91/1.40  tff(c_12, plain, (![A_10, B_12]: (r1_orders_2(A_10, k3_yellow_0(A_10), B_12) | ~m1_subset_1(B_12, u1_struct_0(A_10)) | ~l1_orders_2(A_10) | ~v1_yellow_0(A_10) | ~v5_orders_2(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.91/1.40  tff(c_319, plain, (![D_110, B_111, A_112, C_113]: (r2_hidden(D_110, B_111) | ~r1_orders_2(A_112, C_113, D_110) | ~r2_hidden(C_113, B_111) | ~m1_subset_1(D_110, u1_struct_0(A_112)) | ~m1_subset_1(C_113, u1_struct_0(A_112)) | ~v13_waybel_0(B_111, A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_orders_2(A_112))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.91/1.40  tff(c_332, plain, (![B_118, B_119, A_120]: (r2_hidden(B_118, B_119) | ~r2_hidden(k3_yellow_0(A_120), B_119) | ~m1_subset_1(k3_yellow_0(A_120), u1_struct_0(A_120)) | ~v13_waybel_0(B_119, A_120) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_subset_1(B_118, u1_struct_0(A_120)) | ~l1_orders_2(A_120) | ~v1_yellow_0(A_120) | ~v5_orders_2(A_120) | v2_struct_0(A_120))), inference(resolution, [status(thm)], [c_12, c_319])).
% 2.91/1.40  tff(c_335, plain, (![B_118, B_119]: (r2_hidden(B_118, B_119) | ~r2_hidden(k3_yellow_0('#skF_4'), B_119) | ~v13_waybel_0(B_119, '#skF_4') | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_118, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v1_yellow_0('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_106, c_332])).
% 2.91/1.40  tff(c_340, plain, (![B_118, B_119]: (r2_hidden(B_118, B_119) | ~r2_hidden(k3_yellow_0('#skF_4'), B_119) | ~v13_waybel_0(B_119, '#skF_4') | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_118, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_42, c_40, c_38, c_335])).
% 2.91/1.40  tff(c_343, plain, (![B_121, B_122]: (r2_hidden(B_121, B_122) | ~r2_hidden(k3_yellow_0('#skF_4'), B_122) | ~v13_waybel_0(B_122, '#skF_4') | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_121, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_340])).
% 2.91/1.40  tff(c_348, plain, (![B_121]: (r2_hidden(B_121, '#skF_5') | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v13_waybel_0('#skF_5', '#skF_4') | ~m1_subset_1(B_121, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_30, c_343])).
% 2.91/1.40  tff(c_353, plain, (![B_123]: (r2_hidden(B_123, '#skF_5') | ~m1_subset_1(B_123, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_87, c_348])).
% 2.91/1.40  tff(c_413, plain, (![B_126]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_126), '#skF_5') | u1_struct_0('#skF_4')=B_126 | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_4, c_353])).
% 2.91/1.40  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | B_2=A_1 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.91/1.40  tff(c_421, plain, (u1_struct_0('#skF_4')='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_413, c_2])).
% 2.91/1.40  tff(c_426, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_421])).
% 2.91/1.40  tff(c_88, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_50])).
% 2.91/1.40  tff(c_437, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_426, c_88])).
% 2.91/1.40  tff(c_438, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_426, c_30])).
% 2.91/1.40  tff(c_28, plain, (![B_39]: (~v1_subset_1(B_39, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.91/1.40  tff(c_506, plain, (~v1_subset_1('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_438, c_28])).
% 2.91/1.40  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_437, c_506])).
% 2.91/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.40  
% 2.91/1.40  Inference rules
% 2.91/1.40  ----------------------
% 2.91/1.40  #Ref     : 0
% 2.91/1.40  #Sup     : 77
% 2.91/1.40  #Fact    : 0
% 2.91/1.40  #Define  : 0
% 2.91/1.40  #Split   : 4
% 2.91/1.40  #Chain   : 0
% 2.91/1.40  #Close   : 0
% 2.91/1.40  
% 2.91/1.40  Ordering : KBO
% 2.91/1.40  
% 2.91/1.40  Simplification rules
% 2.91/1.40  ----------------------
% 2.91/1.40  #Subsume      : 2
% 2.91/1.40  #Demod        : 109
% 2.91/1.40  #Tautology    : 22
% 2.91/1.40  #SimpNegUnit  : 11
% 2.91/1.40  #BackRed      : 23
% 2.91/1.40  
% 2.91/1.40  #Partial instantiations: 0
% 2.91/1.40  #Strategies tried      : 1
% 2.91/1.40  
% 2.91/1.40  Timing (in seconds)
% 2.91/1.40  ----------------------
% 2.91/1.40  Preprocessing        : 0.30
% 2.91/1.40  Parsing              : 0.17
% 2.91/1.40  CNF conversion       : 0.02
% 2.91/1.40  Main loop            : 0.33
% 2.91/1.40  Inferencing          : 0.13
% 2.91/1.40  Reduction            : 0.09
% 2.91/1.40  Demodulation         : 0.06
% 2.91/1.40  BG Simplification    : 0.02
% 2.91/1.40  Subsumption          : 0.06
% 2.91/1.40  Abstraction          : 0.02
% 2.91/1.41  MUC search           : 0.00
% 2.91/1.41  Cooper               : 0.00
% 2.91/1.41  Total                : 0.67
% 2.91/1.41  Index Insertion      : 0.00
% 2.91/1.41  Index Deletion       : 0.00
% 2.91/1.41  Index Matching       : 0.00
% 2.91/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
