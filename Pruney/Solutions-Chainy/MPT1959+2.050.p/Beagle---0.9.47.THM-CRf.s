%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:04 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 107 expanded)
%              Number of leaves         :   36 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  142 ( 336 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_yellow_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_139,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_103,axiom,(
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

tff(c_6,plain,(
    ! [A_4] : ~ v1_subset_1('#skF_2'(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1('#skF_2'(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_127,plain,(
    ! [B_61,A_62] :
      ( v1_subset_1(B_61,A_62)
      | B_61 = A_62
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_130,plain,(
    ! [A_4] :
      ( v1_subset_1('#skF_2'(A_4),A_4)
      | '#skF_2'(A_4) = A_4 ) ),
    inference(resolution,[status(thm)],[c_8,c_127])).

tff(c_136,plain,(
    ! [A_4] : '#skF_2'(A_4) = A_4 ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_130])).

tff(c_140,plain,(
    ! [A_4] : ~ v1_subset_1(A_4,A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_6])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | B_2 = A_1
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_46,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_50,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_48,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_40,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_72,plain,(
    ! [A_51,B_52] :
      ( r2_hidden(A_51,B_52)
      | v1_xboole_0(B_52)
      | ~ m1_subset_1(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_69,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_75,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_69])).

tff(c_78,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_75])).

tff(c_58,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_70,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_58])).

tff(c_79,plain,(
    ! [B_53,A_54] :
      ( v1_subset_1(B_53,A_54)
      | B_53 = A_54
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_85,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_38,c_79])).

tff(c_91,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_85])).

tff(c_14,plain,(
    ! [A_10] :
      ( m1_subset_1(k3_yellow_0(A_10),u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_112,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_14])).

tff(c_118,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_112])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_118])).

tff(c_122,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_20,plain,(
    ! [A_14,B_16] :
      ( r1_orders_2(A_14,k3_yellow_0(A_14),B_16)
      | ~ m1_subset_1(B_16,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v1_yellow_0(A_14)
      | ~ v5_orders_2(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_250,plain,(
    ! [D_95,B_96,A_97,C_98] :
      ( r2_hidden(D_95,B_96)
      | ~ r1_orders_2(A_97,C_98,D_95)
      | ~ r2_hidden(C_98,B_96)
      | ~ m1_subset_1(D_95,u1_struct_0(A_97))
      | ~ m1_subset_1(C_98,u1_struct_0(A_97))
      | ~ v13_waybel_0(B_96,A_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_orders_2(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_258,plain,(
    ! [B_101,B_102,A_103] :
      ( r2_hidden(B_101,B_102)
      | ~ r2_hidden(k3_yellow_0(A_103),B_102)
      | ~ m1_subset_1(k3_yellow_0(A_103),u1_struct_0(A_103))
      | ~ v13_waybel_0(B_102,A_103)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(B_101,u1_struct_0(A_103))
      | ~ l1_orders_2(A_103)
      | ~ v1_yellow_0(A_103)
      | ~ v5_orders_2(A_103)
      | v2_struct_0(A_103) ) ),
    inference(resolution,[status(thm)],[c_20,c_250])).

tff(c_262,plain,(
    ! [B_104,B_105,A_106] :
      ( r2_hidden(B_104,B_105)
      | ~ r2_hidden(k3_yellow_0(A_106),B_105)
      | ~ v13_waybel_0(B_105,A_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ m1_subset_1(B_104,u1_struct_0(A_106))
      | ~ v1_yellow_0(A_106)
      | ~ v5_orders_2(A_106)
      | v2_struct_0(A_106)
      | ~ l1_orders_2(A_106) ) ),
    inference(resolution,[status(thm)],[c_14,c_258])).

tff(c_270,plain,(
    ! [B_104] :
      ( r2_hidden(B_104,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_5'))
      | ~ v1_yellow_0('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_262])).

tff(c_275,plain,(
    ! [B_104] :
      ( r2_hidden(B_104,'#skF_6')
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_48,c_40,c_122,c_270])).

tff(c_277,plain,(
    ! [B_107] :
      ( r2_hidden(B_107,'#skF_6')
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_275])).

tff(c_349,plain,(
    ! [B_113] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_113),'#skF_6')
      | u1_struct_0('#skF_5') = B_113
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_277])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | B_2 = A_1
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_353,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_349,c_2])).

tff(c_356,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_353])).

tff(c_121,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_361,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_121])).

tff(c_365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.37  
% 2.46/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.37  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_yellow_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 2.76/1.37  
% 2.76/1.37  %Foreground sorts:
% 2.76/1.37  
% 2.76/1.37  
% 2.76/1.37  %Background operators:
% 2.76/1.37  
% 2.76/1.37  
% 2.76/1.37  %Foreground operators:
% 2.76/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.76/1.37  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 2.76/1.37  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.76/1.37  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.76/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.37  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.76/1.37  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.76/1.37  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.76/1.37  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 2.76/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.76/1.37  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.76/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.76/1.37  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 2.76/1.37  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.76/1.37  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.76/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.37  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.76/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.37  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.76/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.76/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.76/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.76/1.37  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 2.76/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.37  
% 2.76/1.39  tff(f_40, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 2.76/1.39  tff(f_110, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 2.76/1.39  tff(f_139, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 2.76/1.39  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 2.76/1.39  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.76/1.39  tff(f_54, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 2.76/1.39  tff(f_84, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 2.76/1.39  tff(f_103, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 2.76/1.39  tff(c_6, plain, (![A_4]: (~v1_subset_1('#skF_2'(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.39  tff(c_8, plain, (![A_4]: (m1_subset_1('#skF_2'(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.39  tff(c_127, plain, (![B_61, A_62]: (v1_subset_1(B_61, A_62) | B_61=A_62 | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.76/1.39  tff(c_130, plain, (![A_4]: (v1_subset_1('#skF_2'(A_4), A_4) | '#skF_2'(A_4)=A_4)), inference(resolution, [status(thm)], [c_8, c_127])).
% 2.76/1.39  tff(c_136, plain, (![A_4]: ('#skF_2'(A_4)=A_4)), inference(negUnitSimplification, [status(thm)], [c_6, c_130])).
% 2.76/1.39  tff(c_140, plain, (![A_4]: (~v1_subset_1(A_4, A_4))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_6])).
% 2.76/1.39  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.76/1.39  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | B_2=A_1 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.76/1.39  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.76/1.39  tff(c_46, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.76/1.39  tff(c_50, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.76/1.39  tff(c_48, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.76/1.39  tff(c_40, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.76/1.39  tff(c_44, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.76/1.39  tff(c_72, plain, (![A_51, B_52]: (r2_hidden(A_51, B_52) | v1_xboole_0(B_52) | ~m1_subset_1(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.76/1.39  tff(c_64, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.76/1.39  tff(c_69, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_64])).
% 2.76/1.39  tff(c_75, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_72, c_69])).
% 2.76/1.39  tff(c_78, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_44, c_75])).
% 2.76/1.39  tff(c_58, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.76/1.39  tff(c_70, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_69, c_58])).
% 2.76/1.39  tff(c_79, plain, (![B_53, A_54]: (v1_subset_1(B_53, A_54) | B_53=A_54 | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.76/1.39  tff(c_85, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_38, c_79])).
% 2.76/1.39  tff(c_91, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_70, c_85])).
% 2.76/1.39  tff(c_14, plain, (![A_10]: (m1_subset_1(k3_yellow_0(A_10), u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.76/1.39  tff(c_112, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6') | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_91, c_14])).
% 2.76/1.39  tff(c_118, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_112])).
% 2.76/1.39  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_118])).
% 2.76/1.39  tff(c_122, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_64])).
% 2.76/1.39  tff(c_20, plain, (![A_14, B_16]: (r1_orders_2(A_14, k3_yellow_0(A_14), B_16) | ~m1_subset_1(B_16, u1_struct_0(A_14)) | ~l1_orders_2(A_14) | ~v1_yellow_0(A_14) | ~v5_orders_2(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.76/1.39  tff(c_250, plain, (![D_95, B_96, A_97, C_98]: (r2_hidden(D_95, B_96) | ~r1_orders_2(A_97, C_98, D_95) | ~r2_hidden(C_98, B_96) | ~m1_subset_1(D_95, u1_struct_0(A_97)) | ~m1_subset_1(C_98, u1_struct_0(A_97)) | ~v13_waybel_0(B_96, A_97) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_orders_2(A_97))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.76/1.39  tff(c_258, plain, (![B_101, B_102, A_103]: (r2_hidden(B_101, B_102) | ~r2_hidden(k3_yellow_0(A_103), B_102) | ~m1_subset_1(k3_yellow_0(A_103), u1_struct_0(A_103)) | ~v13_waybel_0(B_102, A_103) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(B_101, u1_struct_0(A_103)) | ~l1_orders_2(A_103) | ~v1_yellow_0(A_103) | ~v5_orders_2(A_103) | v2_struct_0(A_103))), inference(resolution, [status(thm)], [c_20, c_250])).
% 2.76/1.39  tff(c_262, plain, (![B_104, B_105, A_106]: (r2_hidden(B_104, B_105) | ~r2_hidden(k3_yellow_0(A_106), B_105) | ~v13_waybel_0(B_105, A_106) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~m1_subset_1(B_104, u1_struct_0(A_106)) | ~v1_yellow_0(A_106) | ~v5_orders_2(A_106) | v2_struct_0(A_106) | ~l1_orders_2(A_106))), inference(resolution, [status(thm)], [c_14, c_258])).
% 2.76/1.39  tff(c_270, plain, (![B_104]: (r2_hidden(B_104, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~m1_subset_1(B_104, u1_struct_0('#skF_5')) | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_262])).
% 2.76/1.39  tff(c_275, plain, (![B_104]: (r2_hidden(B_104, '#skF_6') | ~m1_subset_1(B_104, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_48, c_40, c_122, c_270])).
% 2.76/1.39  tff(c_277, plain, (![B_107]: (r2_hidden(B_107, '#skF_6') | ~m1_subset_1(B_107, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_275])).
% 2.76/1.39  tff(c_349, plain, (![B_113]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_113), '#skF_6') | u1_struct_0('#skF_5')=B_113 | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_4, c_277])).
% 2.76/1.39  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | B_2=A_1 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.76/1.39  tff(c_353, plain, (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_349, c_2])).
% 2.76/1.39  tff(c_356, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_353])).
% 2.76/1.39  tff(c_121, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_64])).
% 2.76/1.39  tff(c_361, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_356, c_121])).
% 2.76/1.39  tff(c_365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_361])).
% 2.76/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.39  
% 2.76/1.39  Inference rules
% 2.76/1.39  ----------------------
% 2.76/1.39  #Ref     : 0
% 2.76/1.39  #Sup     : 49
% 2.76/1.39  #Fact    : 0
% 2.76/1.39  #Define  : 0
% 2.76/1.39  #Split   : 2
% 2.76/1.39  #Chain   : 0
% 2.76/1.39  #Close   : 0
% 2.76/1.39  
% 2.76/1.39  Ordering : KBO
% 2.76/1.39  
% 2.76/1.39  Simplification rules
% 2.76/1.39  ----------------------
% 2.76/1.39  #Subsume      : 6
% 2.76/1.39  #Demod        : 42
% 2.76/1.39  #Tautology    : 23
% 2.76/1.39  #SimpNegUnit  : 11
% 2.76/1.39  #BackRed      : 12
% 2.76/1.39  
% 2.76/1.39  #Partial instantiations: 0
% 2.76/1.39  #Strategies tried      : 1
% 2.76/1.39  
% 2.76/1.39  Timing (in seconds)
% 2.76/1.39  ----------------------
% 2.76/1.39  Preprocessing        : 0.33
% 2.76/1.39  Parsing              : 0.18
% 2.76/1.39  CNF conversion       : 0.03
% 2.76/1.39  Main loop            : 0.29
% 2.76/1.39  Inferencing          : 0.11
% 2.76/1.39  Reduction            : 0.08
% 2.76/1.39  Demodulation         : 0.05
% 2.76/1.39  BG Simplification    : 0.02
% 2.76/1.39  Subsumption          : 0.05
% 2.76/1.39  Abstraction          : 0.01
% 2.76/1.39  MUC search           : 0.00
% 2.76/1.39  Cooper               : 0.00
% 2.76/1.39  Total                : 0.65
% 2.76/1.39  Index Insertion      : 0.00
% 2.76/1.39  Index Deletion       : 0.00
% 2.76/1.39  Index Matching       : 0.00
% 2.76/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
