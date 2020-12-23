%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:30 EST 2020

% Result     : Theorem 7.72s
% Output     : CNFRefutation 7.72s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 747 expanded)
%              Number of leaves         :   37 ( 291 expanded)
%              Depth                    :   19
%              Number of atoms          :  219 (2187 expanded)
%              Number of equality atoms :   32 ( 450 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_101,axiom,(
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

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_mcart_1)).

tff(f_132,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_85,axiom,(
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

tff(c_42,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_26,plain,(
    ! [A_34] :
      ( l1_struct_0(A_34)
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_63,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_69,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_orders_2(A_53) ) ),
    inference(resolution,[status(thm)],[c_26,c_63])).

tff(c_73,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_69])).

tff(c_78,plain,(
    ! [A_54] :
      ( ~ v1_xboole_0(u1_struct_0(A_54))
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_81,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_78])).

tff(c_82,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_81])).

tff(c_83,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_87,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_83])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_87])).

tff(c_92,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_48,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_46,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_44,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_6128,plain,(
    ! [A_531,B_532] :
      ( k2_orders_2(A_531,B_532) = a_2_1_orders_2(A_531,B_532)
      | ~ m1_subset_1(B_532,k1_zfmisc_1(u1_struct_0(A_531)))
      | ~ l1_orders_2(A_531)
      | ~ v5_orders_2(A_531)
      | ~ v4_orders_2(A_531)
      | ~ v3_orders_2(A_531)
      | v2_struct_0(A_531) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6139,plain,(
    ! [B_532] :
      ( k2_orders_2('#skF_4',B_532) = a_2_1_orders_2('#skF_4',B_532)
      | ~ m1_subset_1(B_532,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_6128])).

tff(c_6147,plain,(
    ! [B_532] :
      ( k2_orders_2('#skF_4',B_532) = a_2_1_orders_2('#skF_4',B_532)
      | ~ m1_subset_1(B_532,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_6139])).

tff(c_6150,plain,(
    ! [B_533] :
      ( k2_orders_2('#skF_4',B_533) = a_2_1_orders_2('#skF_4',B_533)
      | ~ m1_subset_1(B_533,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_6147])).

tff(c_6171,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_51,c_6150])).

tff(c_40,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_6177,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6171,c_40])).

tff(c_12,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6196,plain,(
    ! [A_536,B_537,C_538] :
      ( '#skF_2'(A_536,B_537,C_538) = A_536
      | ~ r2_hidden(A_536,a_2_1_orders_2(B_537,C_538))
      | ~ m1_subset_1(C_538,k1_zfmisc_1(u1_struct_0(B_537)))
      | ~ l1_orders_2(B_537)
      | ~ v5_orders_2(B_537)
      | ~ v4_orders_2(B_537)
      | ~ v3_orders_2(B_537)
      | v2_struct_0(B_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_7242,plain,(
    ! [B_623,C_624] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2(B_623,C_624)),B_623,C_624) = '#skF_1'(a_2_1_orders_2(B_623,C_624))
      | ~ m1_subset_1(C_624,k1_zfmisc_1(u1_struct_0(B_623)))
      | ~ l1_orders_2(B_623)
      | ~ v5_orders_2(B_623)
      | ~ v4_orders_2(B_623)
      | ~ v3_orders_2(B_623)
      | v2_struct_0(B_623)
      | a_2_1_orders_2(B_623,C_624) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_6196])).

tff(c_7250,plain,(
    ! [C_624] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_624)),'#skF_4',C_624) = '#skF_1'(a_2_1_orders_2('#skF_4',C_624))
      | ~ m1_subset_1(C_624,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_624) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_7242])).

tff(c_7257,plain,(
    ! [C_624] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_624)),'#skF_4',C_624) = '#skF_1'(a_2_1_orders_2('#skF_4',C_624))
      | ~ m1_subset_1(C_624,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_624) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_7250])).

tff(c_7260,plain,(
    ! [C_625] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_625)),'#skF_4',C_625) = '#skF_1'(a_2_1_orders_2('#skF_4',C_625))
      | ~ m1_subset_1(C_625,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_1_orders_2('#skF_4',C_625) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_7257])).

tff(c_7277,plain,
    ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_7260])).

tff(c_7289,plain,(
    '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6177,c_7277])).

tff(c_38,plain,(
    ! [A_35,B_36,C_37] :
      ( m1_subset_1('#skF_2'(A_35,B_36,C_37),u1_struct_0(B_36))
      | ~ r2_hidden(A_35,a_2_1_orders_2(B_36,C_37))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(B_36)))
      | ~ l1_orders_2(B_36)
      | ~ v5_orders_2(B_36)
      | ~ v4_orders_2(B_36)
      | ~ v3_orders_2(B_36)
      | v2_struct_0(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_7296,plain,
    ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),u1_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7289,c_38])).

tff(c_7302,plain,
    ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_51,c_73,c_73,c_7296])).

tff(c_7303,plain,
    ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_7302])).

tff(c_7428,plain,(
    ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_7303])).

tff(c_7434,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_7428])).

tff(c_7440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6177,c_7434])).

tff(c_7441,plain,(
    m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7303])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7442,plain,(
    r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_7303])).

tff(c_6925,plain,(
    ! [B_594,A_595,C_596,E_597] :
      ( r2_orders_2(B_594,'#skF_2'(A_595,B_594,C_596),E_597)
      | ~ r2_hidden(E_597,C_596)
      | ~ m1_subset_1(E_597,u1_struct_0(B_594))
      | ~ r2_hidden(A_595,a_2_1_orders_2(B_594,C_596))
      | ~ m1_subset_1(C_596,k1_zfmisc_1(u1_struct_0(B_594)))
      | ~ l1_orders_2(B_594)
      | ~ v5_orders_2(B_594)
      | ~ v4_orders_2(B_594)
      | ~ v3_orders_2(B_594)
      | v2_struct_0(B_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_7367,plain,(
    ! [B_626,A_627,E_628] :
      ( r2_orders_2(B_626,'#skF_2'(A_627,B_626,u1_struct_0(B_626)),E_628)
      | ~ r2_hidden(E_628,u1_struct_0(B_626))
      | ~ m1_subset_1(E_628,u1_struct_0(B_626))
      | ~ r2_hidden(A_627,a_2_1_orders_2(B_626,u1_struct_0(B_626)))
      | ~ l1_orders_2(B_626)
      | ~ v5_orders_2(B_626)
      | ~ v4_orders_2(B_626)
      | ~ v3_orders_2(B_626)
      | v2_struct_0(B_626) ) ),
    inference(resolution,[status(thm)],[c_51,c_6925])).

tff(c_7378,plain,(
    ! [A_627,E_628] :
      ( r2_orders_2('#skF_4','#skF_2'(A_627,'#skF_4',k2_struct_0('#skF_4')),E_628)
      | ~ r2_hidden(E_628,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_628,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_627,a_2_1_orders_2('#skF_4',u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_7367])).

tff(c_7383,plain,(
    ! [A_627,E_628] :
      ( r2_orders_2('#skF_4','#skF_2'(A_627,'#skF_4',k2_struct_0('#skF_4')),E_628)
      | ~ r2_hidden(E_628,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_628,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_627,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_73,c_73,c_73,c_7378])).

tff(c_7494,plain,(
    ! [A_633,E_634] :
      ( r2_orders_2('#skF_4','#skF_2'(A_633,'#skF_4',k2_struct_0('#skF_4')),E_634)
      | ~ r2_hidden(E_634,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_634,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_633,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_7383])).

tff(c_7505,plain,(
    ! [E_634] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_634)
      | ~ r2_hidden(E_634,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_634,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7289,c_7494])).

tff(c_7518,plain,(
    ! [E_635] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_635)
      | ~ r2_hidden(E_635,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_635,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7442,c_7505])).

tff(c_20,plain,(
    ! [A_24,C_30] :
      ( ~ r2_orders_2(A_24,C_30,C_30)
      | ~ m1_subset_1(C_30,u1_struct_0(A_24))
      | ~ l1_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7526,plain,
    ( ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_7518,c_20])).

tff(c_7536,plain,(
    ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7441,c_42,c_7441,c_73,c_7526])).

tff(c_7539,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_7536])).

tff(c_7542,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7441,c_7539])).

tff(c_7544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_7542])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.72/2.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.72/2.78  
% 7.72/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.72/2.78  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 7.72/2.78  
% 7.72/2.78  %Foreground sorts:
% 7.72/2.78  
% 7.72/2.78  
% 7.72/2.78  %Background operators:
% 7.72/2.78  
% 7.72/2.78  
% 7.72/2.78  %Foreground operators:
% 7.72/2.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.72/2.78  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.72/2.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.72/2.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.72/2.78  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.72/2.78  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.72/2.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.72/2.78  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 7.72/2.78  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 7.72/2.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.72/2.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.72/2.78  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.72/2.78  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.72/2.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.72/2.78  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.72/2.78  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.72/2.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.72/2.78  tff('#skF_4', type, '#skF_4': $i).
% 7.72/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.72/2.78  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 7.72/2.78  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.72/2.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.72/2.78  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.72/2.78  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.72/2.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.72/2.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.72/2.78  
% 7.72/2.79  tff(f_146, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_orders_2)).
% 7.72/2.79  tff(f_105, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 7.72/2.79  tff(f_62, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 7.72/2.79  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 7.72/2.79  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 7.72/2.79  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.72/2.79  tff(f_101, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 7.72/2.79  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: (((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_mcart_1)).
% 7.72/2.79  tff(f_132, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 7.72/2.79  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 7.72/2.79  tff(f_85, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 7.72/2.79  tff(c_42, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.72/2.79  tff(c_26, plain, (![A_34]: (l1_struct_0(A_34) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.72/2.79  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.72/2.79  tff(c_63, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.72/2.79  tff(c_69, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_orders_2(A_53))), inference(resolution, [status(thm)], [c_26, c_63])).
% 7.72/2.79  tff(c_73, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_69])).
% 7.72/2.79  tff(c_78, plain, (![A_54]: (~v1_xboole_0(u1_struct_0(A_54)) | ~l1_struct_0(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.72/2.79  tff(c_81, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_73, c_78])).
% 7.72/2.79  tff(c_82, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_81])).
% 7.72/2.79  tff(c_83, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_82])).
% 7.72/2.79  tff(c_87, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_26, c_83])).
% 7.72/2.79  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_87])).
% 7.72/2.79  tff(c_92, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_82])).
% 7.72/2.79  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.72/2.79  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.72/2.79  tff(c_51, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 7.72/2.79  tff(c_48, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.72/2.79  tff(c_46, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.72/2.79  tff(c_44, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.72/2.79  tff(c_6128, plain, (![A_531, B_532]: (k2_orders_2(A_531, B_532)=a_2_1_orders_2(A_531, B_532) | ~m1_subset_1(B_532, k1_zfmisc_1(u1_struct_0(A_531))) | ~l1_orders_2(A_531) | ~v5_orders_2(A_531) | ~v4_orders_2(A_531) | ~v3_orders_2(A_531) | v2_struct_0(A_531))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.72/2.79  tff(c_6139, plain, (![B_532]: (k2_orders_2('#skF_4', B_532)=a_2_1_orders_2('#skF_4', B_532) | ~m1_subset_1(B_532, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_6128])).
% 7.72/2.79  tff(c_6147, plain, (![B_532]: (k2_orders_2('#skF_4', B_532)=a_2_1_orders_2('#skF_4', B_532) | ~m1_subset_1(B_532, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_6139])).
% 7.72/2.79  tff(c_6150, plain, (![B_533]: (k2_orders_2('#skF_4', B_533)=a_2_1_orders_2('#skF_4', B_533) | ~m1_subset_1(B_533, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_6147])).
% 7.72/2.79  tff(c_6171, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_51, c_6150])).
% 7.72/2.79  tff(c_40, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.72/2.79  tff(c_6177, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6171, c_40])).
% 7.72/2.79  tff(c_12, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.72/2.79  tff(c_6196, plain, (![A_536, B_537, C_538]: ('#skF_2'(A_536, B_537, C_538)=A_536 | ~r2_hidden(A_536, a_2_1_orders_2(B_537, C_538)) | ~m1_subset_1(C_538, k1_zfmisc_1(u1_struct_0(B_537))) | ~l1_orders_2(B_537) | ~v5_orders_2(B_537) | ~v4_orders_2(B_537) | ~v3_orders_2(B_537) | v2_struct_0(B_537))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.72/2.79  tff(c_7242, plain, (![B_623, C_624]: ('#skF_2'('#skF_1'(a_2_1_orders_2(B_623, C_624)), B_623, C_624)='#skF_1'(a_2_1_orders_2(B_623, C_624)) | ~m1_subset_1(C_624, k1_zfmisc_1(u1_struct_0(B_623))) | ~l1_orders_2(B_623) | ~v5_orders_2(B_623) | ~v4_orders_2(B_623) | ~v3_orders_2(B_623) | v2_struct_0(B_623) | a_2_1_orders_2(B_623, C_624)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_6196])).
% 7.72/2.79  tff(c_7250, plain, (![C_624]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_624)), '#skF_4', C_624)='#skF_1'(a_2_1_orders_2('#skF_4', C_624)) | ~m1_subset_1(C_624, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_624)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_73, c_7242])).
% 7.72/2.79  tff(c_7257, plain, (![C_624]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_624)), '#skF_4', C_624)='#skF_1'(a_2_1_orders_2('#skF_4', C_624)) | ~m1_subset_1(C_624, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_624)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_7250])).
% 7.72/2.79  tff(c_7260, plain, (![C_625]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_625)), '#skF_4', C_625)='#skF_1'(a_2_1_orders_2('#skF_4', C_625)) | ~m1_subset_1(C_625, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', C_625)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_50, c_7257])).
% 7.72/2.79  tff(c_7277, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_51, c_7260])).
% 7.72/2.79  tff(c_7289, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_6177, c_7277])).
% 7.72/2.79  tff(c_38, plain, (![A_35, B_36, C_37]: (m1_subset_1('#skF_2'(A_35, B_36, C_37), u1_struct_0(B_36)) | ~r2_hidden(A_35, a_2_1_orders_2(B_36, C_37)) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(B_36))) | ~l1_orders_2(B_36) | ~v5_orders_2(B_36) | ~v4_orders_2(B_36) | ~v3_orders_2(B_36) | v2_struct_0(B_36))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.72/2.79  tff(c_7296, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7289, c_38])).
% 7.72/2.79  tff(c_7302, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_51, c_73, c_73, c_7296])).
% 7.72/2.79  tff(c_7303, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_50, c_7302])).
% 7.72/2.79  tff(c_7428, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_7303])).
% 7.72/2.79  tff(c_7434, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_7428])).
% 7.72/2.79  tff(c_7440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6177, c_7434])).
% 7.72/2.79  tff(c_7441, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_7303])).
% 7.72/2.79  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.72/2.79  tff(c_7442, plain, (r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_7303])).
% 7.72/2.79  tff(c_6925, plain, (![B_594, A_595, C_596, E_597]: (r2_orders_2(B_594, '#skF_2'(A_595, B_594, C_596), E_597) | ~r2_hidden(E_597, C_596) | ~m1_subset_1(E_597, u1_struct_0(B_594)) | ~r2_hidden(A_595, a_2_1_orders_2(B_594, C_596)) | ~m1_subset_1(C_596, k1_zfmisc_1(u1_struct_0(B_594))) | ~l1_orders_2(B_594) | ~v5_orders_2(B_594) | ~v4_orders_2(B_594) | ~v3_orders_2(B_594) | v2_struct_0(B_594))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.72/2.79  tff(c_7367, plain, (![B_626, A_627, E_628]: (r2_orders_2(B_626, '#skF_2'(A_627, B_626, u1_struct_0(B_626)), E_628) | ~r2_hidden(E_628, u1_struct_0(B_626)) | ~m1_subset_1(E_628, u1_struct_0(B_626)) | ~r2_hidden(A_627, a_2_1_orders_2(B_626, u1_struct_0(B_626))) | ~l1_orders_2(B_626) | ~v5_orders_2(B_626) | ~v4_orders_2(B_626) | ~v3_orders_2(B_626) | v2_struct_0(B_626))), inference(resolution, [status(thm)], [c_51, c_6925])).
% 7.72/2.79  tff(c_7378, plain, (![A_627, E_628]: (r2_orders_2('#skF_4', '#skF_2'(A_627, '#skF_4', k2_struct_0('#skF_4')), E_628) | ~r2_hidden(E_628, u1_struct_0('#skF_4')) | ~m1_subset_1(E_628, u1_struct_0('#skF_4')) | ~r2_hidden(A_627, a_2_1_orders_2('#skF_4', u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_7367])).
% 7.72/2.79  tff(c_7383, plain, (![A_627, E_628]: (r2_orders_2('#skF_4', '#skF_2'(A_627, '#skF_4', k2_struct_0('#skF_4')), E_628) | ~r2_hidden(E_628, k2_struct_0('#skF_4')) | ~m1_subset_1(E_628, k2_struct_0('#skF_4')) | ~r2_hidden(A_627, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_73, c_73, c_73, c_7378])).
% 7.72/2.79  tff(c_7494, plain, (![A_633, E_634]: (r2_orders_2('#skF_4', '#skF_2'(A_633, '#skF_4', k2_struct_0('#skF_4')), E_634) | ~r2_hidden(E_634, k2_struct_0('#skF_4')) | ~m1_subset_1(E_634, k2_struct_0('#skF_4')) | ~r2_hidden(A_633, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_7383])).
% 7.72/2.79  tff(c_7505, plain, (![E_634]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_634) | ~r2_hidden(E_634, k2_struct_0('#skF_4')) | ~m1_subset_1(E_634, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_7289, c_7494])).
% 7.72/2.79  tff(c_7518, plain, (![E_635]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_635) | ~r2_hidden(E_635, k2_struct_0('#skF_4')) | ~m1_subset_1(E_635, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_7442, c_7505])).
% 7.72/2.79  tff(c_20, plain, (![A_24, C_30]: (~r2_orders_2(A_24, C_30, C_30) | ~m1_subset_1(C_30, u1_struct_0(A_24)) | ~l1_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.72/2.79  tff(c_7526, plain, (~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_7518, c_20])).
% 7.72/2.79  tff(c_7536, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7441, c_42, c_7441, c_73, c_7526])).
% 7.72/2.79  tff(c_7539, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_7536])).
% 7.72/2.79  tff(c_7542, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7441, c_7539])).
% 7.72/2.79  tff(c_7544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_7542])).
% 7.72/2.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.72/2.79  
% 7.72/2.79  Inference rules
% 7.72/2.79  ----------------------
% 7.72/2.79  #Ref     : 0
% 7.72/2.79  #Sup     : 1645
% 7.72/2.79  #Fact    : 0
% 7.72/2.79  #Define  : 0
% 7.72/2.79  #Split   : 34
% 7.72/2.79  #Chain   : 0
% 7.72/2.79  #Close   : 0
% 7.72/2.79  
% 7.72/2.79  Ordering : KBO
% 7.72/2.79  
% 7.72/2.79  Simplification rules
% 7.72/2.79  ----------------------
% 7.72/2.79  #Subsume      : 143
% 7.72/2.79  #Demod        : 1506
% 7.72/2.79  #Tautology    : 384
% 7.72/2.79  #SimpNegUnit  : 206
% 7.72/2.79  #BackRed      : 27
% 7.72/2.79  
% 7.72/2.79  #Partial instantiations: 0
% 7.72/2.79  #Strategies tried      : 1
% 7.72/2.79  
% 7.72/2.79  Timing (in seconds)
% 7.72/2.79  ----------------------
% 7.72/2.80  Preprocessing        : 0.33
% 7.72/2.80  Parsing              : 0.17
% 7.72/2.80  CNF conversion       : 0.02
% 7.72/2.80  Main loop            : 1.69
% 7.72/2.80  Inferencing          : 0.54
% 7.72/2.80  Reduction            : 0.50
% 7.72/2.80  Demodulation         : 0.34
% 7.72/2.80  BG Simplification    : 0.07
% 7.72/2.80  Subsumption          : 0.44
% 7.72/2.80  Abstraction          : 0.09
% 7.72/2.80  MUC search           : 0.00
% 7.72/2.80  Cooper               : 0.00
% 7.72/2.80  Total                : 2.06
% 7.72/2.80  Index Insertion      : 0.00
% 7.72/2.80  Index Deletion       : 0.00
% 7.72/2.80  Index Matching       : 0.00
% 7.72/2.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
