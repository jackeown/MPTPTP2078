%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:03 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 147 expanded)
%              Number of leaves         :   32 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  151 ( 604 expanded)
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

tff(f_126,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_90,axiom,(
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

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1('#skF_1'(A_3,B_4),A_3)
      | B_4 = A_3
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    v13_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_92,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_95,plain,
    ( ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_92])).

tff(c_98,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_95])).

tff(c_44,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_56,plain,
    ( r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_99,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_56])).

tff(c_106,plain,(
    ! [B_53,A_54] :
      ( v1_subset_1(B_53,A_54)
      | B_53 = A_54
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_113,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36,c_106])).

tff(c_117,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_113])).

tff(c_16,plain,(
    ! [A_9] :
      ( m1_subset_1(k3_yellow_0(A_9),u1_struct_0(A_9))
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_127,plain,
    ( m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_16])).

tff(c_133,plain,(
    m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_127])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_133])).

tff(c_137,plain,(
    r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_48,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_46,plain,(
    v1_yellow_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_163,plain,(
    ! [A_59,C_60,B_61] :
      ( m1_subset_1(A_59,C_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(C_60))
      | ~ r2_hidden(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_170,plain,(
    ! [A_59] :
      ( m1_subset_1(A_59,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_59,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_163])).

tff(c_18,plain,(
    ! [A_10,B_12] :
      ( r1_orders_2(A_10,k3_yellow_0(A_10),B_12)
      | ~ m1_subset_1(B_12,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10)
      | ~ v1_yellow_0(A_10)
      | ~ v5_orders_2(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_350,plain,(
    ! [D_105,B_106,A_107,C_108] :
      ( r2_hidden(D_105,B_106)
      | ~ r1_orders_2(A_107,C_108,D_105)
      | ~ r2_hidden(C_108,B_106)
      | ~ m1_subset_1(D_105,u1_struct_0(A_107))
      | ~ m1_subset_1(C_108,u1_struct_0(A_107))
      | ~ v13_waybel_0(B_106,A_107)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_orders_2(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_380,plain,(
    ! [B_121,B_122,A_123] :
      ( r2_hidden(B_121,B_122)
      | ~ r2_hidden(k3_yellow_0(A_123),B_122)
      | ~ m1_subset_1(k3_yellow_0(A_123),u1_struct_0(A_123))
      | ~ v13_waybel_0(B_122,A_123)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(B_121,u1_struct_0(A_123))
      | ~ l1_orders_2(A_123)
      | ~ v1_yellow_0(A_123)
      | ~ v5_orders_2(A_123)
      | v2_struct_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_18,c_350])).

tff(c_383,plain,(
    ! [B_121,B_122] :
      ( r2_hidden(B_121,B_122)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_122)
      | ~ v13_waybel_0(B_122,'#skF_4')
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v1_yellow_0('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_170,c_380])).

tff(c_391,plain,(
    ! [B_121,B_122] :
      ( r2_hidden(B_121,B_122)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_122)
      | ~ v13_waybel_0(B_122,'#skF_4')
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_48,c_46,c_44,c_383])).

tff(c_395,plain,(
    ! [B_124,B_125] :
      ( r2_hidden(B_124,B_125)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_125)
      | ~ v13_waybel_0(B_125,'#skF_4')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_124,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_391])).

tff(c_403,plain,(
    ! [B_124] :
      ( r2_hidden(B_124,'#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
      | ~ v13_waybel_0('#skF_5','#skF_4')
      | ~ m1_subset_1(B_124,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_36,c_395])).

tff(c_409,plain,(
    ! [B_126] :
      ( r2_hidden(B_126,'#skF_5')
      | ~ m1_subset_1(B_126,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_137,c_403])).

tff(c_482,plain,(
    ! [B_131] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_131),'#skF_5')
      | u1_struct_0('#skF_4') = B_131
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_12,c_409])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | B_4 = A_3
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_492,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_482,c_10])).

tff(c_501,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_492])).

tff(c_136,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_516,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_136])).

tff(c_518,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_36])).

tff(c_34,plain,(
    ! [B_39] :
      ( ~ v1_subset_1(B_39,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_616,plain,(
    ~ v1_subset_1('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_518,c_34])).

tff(c_627,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_616])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:28:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.40  
% 2.90/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.40  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.90/1.40  
% 2.90/1.40  %Foreground sorts:
% 2.90/1.40  
% 2.90/1.40  
% 2.90/1.40  %Background operators:
% 2.90/1.40  
% 2.90/1.40  
% 2.90/1.40  %Foreground operators:
% 2.90/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.90/1.40  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.90/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.40  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.90/1.40  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.90/1.40  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.90/1.40  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 2.90/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.90/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.90/1.40  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.90/1.40  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.90/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.40  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.90/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.90/1.40  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.90/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.90/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.90/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.90/1.40  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 2.90/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.40  
% 2.90/1.42  tff(f_126, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 2.90/1.42  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 2.90/1.42  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.90/1.42  tff(f_97, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.90/1.42  tff(f_57, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 2.90/1.42  tff(f_53, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.90/1.42  tff(f_71, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_yellow_0)).
% 2.90/1.42  tff(f_90, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 2.90/1.42  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.90/1.42  tff(c_12, plain, (![A_3, B_4]: (m1_subset_1('#skF_1'(A_3, B_4), A_3) | B_4=A_3 | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.90/1.42  tff(c_38, plain, (v13_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.90/1.42  tff(c_42, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.90/1.42  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.90/1.42  tff(c_62, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.90/1.42  tff(c_92, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_62])).
% 2.90/1.42  tff(c_95, plain, (~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_92])).
% 2.90/1.42  tff(c_98, plain, (~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_95])).
% 2.90/1.42  tff(c_44, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.90/1.42  tff(c_56, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.90/1.42  tff(c_99, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_92, c_56])).
% 2.90/1.42  tff(c_106, plain, (![B_53, A_54]: (v1_subset_1(B_53, A_54) | B_53=A_54 | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.90/1.42  tff(c_113, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_36, c_106])).
% 2.90/1.42  tff(c_117, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_99, c_113])).
% 2.90/1.42  tff(c_16, plain, (![A_9]: (m1_subset_1(k3_yellow_0(A_9), u1_struct_0(A_9)) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.90/1.42  tff(c_127, plain, (m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5') | ~l1_orders_2('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_117, c_16])).
% 2.90/1.42  tff(c_133, plain, (m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_127])).
% 2.90/1.42  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_133])).
% 2.90/1.42  tff(c_137, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_62])).
% 2.90/1.42  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.90/1.42  tff(c_48, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.90/1.42  tff(c_46, plain, (v1_yellow_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.90/1.42  tff(c_163, plain, (![A_59, C_60, B_61]: (m1_subset_1(A_59, C_60) | ~m1_subset_1(B_61, k1_zfmisc_1(C_60)) | ~r2_hidden(A_59, B_61))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.90/1.42  tff(c_170, plain, (![A_59]: (m1_subset_1(A_59, u1_struct_0('#skF_4')) | ~r2_hidden(A_59, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_163])).
% 2.90/1.42  tff(c_18, plain, (![A_10, B_12]: (r1_orders_2(A_10, k3_yellow_0(A_10), B_12) | ~m1_subset_1(B_12, u1_struct_0(A_10)) | ~l1_orders_2(A_10) | ~v1_yellow_0(A_10) | ~v5_orders_2(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.90/1.42  tff(c_350, plain, (![D_105, B_106, A_107, C_108]: (r2_hidden(D_105, B_106) | ~r1_orders_2(A_107, C_108, D_105) | ~r2_hidden(C_108, B_106) | ~m1_subset_1(D_105, u1_struct_0(A_107)) | ~m1_subset_1(C_108, u1_struct_0(A_107)) | ~v13_waybel_0(B_106, A_107) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_orders_2(A_107))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.90/1.42  tff(c_380, plain, (![B_121, B_122, A_123]: (r2_hidden(B_121, B_122) | ~r2_hidden(k3_yellow_0(A_123), B_122) | ~m1_subset_1(k3_yellow_0(A_123), u1_struct_0(A_123)) | ~v13_waybel_0(B_122, A_123) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_subset_1(B_121, u1_struct_0(A_123)) | ~l1_orders_2(A_123) | ~v1_yellow_0(A_123) | ~v5_orders_2(A_123) | v2_struct_0(A_123))), inference(resolution, [status(thm)], [c_18, c_350])).
% 2.90/1.42  tff(c_383, plain, (![B_121, B_122]: (r2_hidden(B_121, B_122) | ~r2_hidden(k3_yellow_0('#skF_4'), B_122) | ~v13_waybel_0(B_122, '#skF_4') | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_121, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v1_yellow_0('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_170, c_380])).
% 2.90/1.42  tff(c_391, plain, (![B_121, B_122]: (r2_hidden(B_121, B_122) | ~r2_hidden(k3_yellow_0('#skF_4'), B_122) | ~v13_waybel_0(B_122, '#skF_4') | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_121, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_48, c_46, c_44, c_383])).
% 2.90/1.42  tff(c_395, plain, (![B_124, B_125]: (r2_hidden(B_124, B_125) | ~r2_hidden(k3_yellow_0('#skF_4'), B_125) | ~v13_waybel_0(B_125, '#skF_4') | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_124, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_391])).
% 2.90/1.42  tff(c_403, plain, (![B_124]: (r2_hidden(B_124, '#skF_5') | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v13_waybel_0('#skF_5', '#skF_4') | ~m1_subset_1(B_124, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_36, c_395])).
% 2.90/1.42  tff(c_409, plain, (![B_126]: (r2_hidden(B_126, '#skF_5') | ~m1_subset_1(B_126, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_137, c_403])).
% 2.90/1.42  tff(c_482, plain, (![B_131]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_131), '#skF_5') | u1_struct_0('#skF_4')=B_131 | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_12, c_409])).
% 2.90/1.42  tff(c_10, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | B_4=A_3 | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.90/1.42  tff(c_492, plain, (u1_struct_0('#skF_4')='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_482, c_10])).
% 2.90/1.42  tff(c_501, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_492])).
% 2.90/1.42  tff(c_136, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_62])).
% 2.90/1.42  tff(c_516, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_501, c_136])).
% 2.90/1.42  tff(c_518, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_36])).
% 2.90/1.42  tff(c_34, plain, (![B_39]: (~v1_subset_1(B_39, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.90/1.42  tff(c_616, plain, (~v1_subset_1('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_518, c_34])).
% 2.90/1.42  tff(c_627, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_516, c_616])).
% 2.90/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.42  
% 2.90/1.42  Inference rules
% 2.90/1.42  ----------------------
% 2.90/1.42  #Ref     : 0
% 2.90/1.42  #Sup     : 106
% 2.90/1.42  #Fact    : 0
% 2.90/1.42  #Define  : 0
% 2.90/1.42  #Split   : 3
% 2.90/1.42  #Chain   : 0
% 2.90/1.42  #Close   : 0
% 2.90/1.42  
% 2.90/1.42  Ordering : KBO
% 2.90/1.42  
% 2.90/1.42  Simplification rules
% 2.90/1.42  ----------------------
% 2.90/1.42  #Subsume      : 24
% 2.90/1.42  #Demod        : 91
% 2.90/1.42  #Tautology    : 23
% 2.90/1.42  #SimpNegUnit  : 13
% 2.90/1.42  #BackRed      : 17
% 2.90/1.42  
% 2.90/1.42  #Partial instantiations: 0
% 2.90/1.42  #Strategies tried      : 1
% 2.90/1.42  
% 2.90/1.42  Timing (in seconds)
% 2.90/1.42  ----------------------
% 2.90/1.42  Preprocessing        : 0.30
% 2.90/1.42  Parsing              : 0.16
% 2.90/1.42  CNF conversion       : 0.02
% 2.90/1.42  Main loop            : 0.35
% 2.90/1.42  Inferencing          : 0.13
% 2.90/1.42  Reduction            : 0.09
% 2.90/1.42  Demodulation         : 0.06
% 2.90/1.42  BG Simplification    : 0.02
% 2.90/1.42  Subsumption          : 0.07
% 2.90/1.42  Abstraction          : 0.02
% 2.90/1.42  MUC search           : 0.00
% 2.90/1.42  Cooper               : 0.00
% 2.90/1.42  Total                : 0.69
% 2.90/1.42  Index Insertion      : 0.00
% 2.90/1.42  Index Deletion       : 0.00
% 2.90/1.42  Index Matching       : 0.00
% 2.90/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
