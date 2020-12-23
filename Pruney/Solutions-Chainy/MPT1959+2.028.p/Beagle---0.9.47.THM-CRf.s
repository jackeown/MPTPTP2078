%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:01 EST 2020

% Result     : Theorem 17.56s
% Output     : CNFRefutation 17.83s
% Verified   : 
% Statistics : Number of formulae       :  354 (3075 expanded)
%              Number of leaves         :   45 (1102 expanded)
%              Depth                    :   31
%              Number of atoms          : 1445 (14739 expanded)
%              Number of equality atoms :  164 ( 772 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(k5_waybel_0,type,(
    k5_waybel_0: ( $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_31,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_128,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_157,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r1_yellow_0(A,k5_waybel_0(A,B))
            & k1_yellow_0(A,k5_waybel_0(A,B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_waybel_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( ( r1_tarski(B,C)
            & r1_yellow_0(A,B)
            & r1_yellow_0(A,C) )
         => r1_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow_0)).

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

tff(c_4,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k2_subset_1(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_3] : m1_subset_1(A_3,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_44,plain,(
    ! [B_49] :
      ( ~ v1_subset_1(B_49,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_75,plain,(
    ! [B_49] : ~ v1_subset_1(B_49,B_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_44])).

tff(c_48,plain,(
    v13_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_100,plain,(
    ! [A_57,B_58] :
      ( r2_hidden(A_57,B_58)
      | v1_xboole_0(B_58)
      | ~ m1_subset_1(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_66,plain,
    ( r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_98,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_99,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_72])).

tff(c_103,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_99])).

tff(c_106,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_103])).

tff(c_54,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_107,plain,(
    ! [B_59,A_60] :
      ( v1_subset_1(B_59,A_60)
      | B_59 = A_60
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_110,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_107])).

tff(c_116,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_110])).

tff(c_18,plain,(
    ! [A_13] :
      ( m1_subset_1(k3_yellow_0(A_13),u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_127,plain,
    ( m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_18])).

tff(c_131,plain,(
    m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_127])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_131])).

tff(c_134,plain,(
    r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1('#skF_1'(A_4,B_5),A_4)
      | B_5 = A_4
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_62,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_60,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_58,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_40,plain,(
    ! [A_45,B_47] :
      ( r1_yellow_0(A_45,k5_waybel_0(A_45,B_47))
      | ~ m1_subset_1(B_47,u1_struct_0(A_45))
      | ~ l1_orders_2(A_45)
      | ~ v5_orders_2(A_45)
      | ~ v4_orders_2(A_45)
      | ~ v3_orders_2(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_28194,plain,(
    ! [A_1691,B_1692] :
      ( k1_yellow_0(A_1691,k5_waybel_0(A_1691,B_1692)) = B_1692
      | ~ m1_subset_1(B_1692,u1_struct_0(A_1691))
      | ~ l1_orders_2(A_1691)
      | ~ v5_orders_2(A_1691)
      | ~ v4_orders_2(A_1691)
      | ~ v3_orders_2(A_1691)
      | v2_struct_0(A_1691) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_28211,plain,(
    ! [A_1691,B_5] :
      ( k1_yellow_0(A_1691,k5_waybel_0(A_1691,'#skF_1'(u1_struct_0(A_1691),B_5))) = '#skF_1'(u1_struct_0(A_1691),B_5)
      | ~ l1_orders_2(A_1691)
      | ~ v5_orders_2(A_1691)
      | ~ v4_orders_2(A_1691)
      | ~ v3_orders_2(A_1691)
      | v2_struct_0(A_1691)
      | u1_struct_0(A_1691) = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_1691))) ) ),
    inference(resolution,[status(thm)],[c_10,c_28194])).

tff(c_152,plain,(
    ! [A_65,C_66,B_67] :
      ( m1_subset_1(A_65,C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_157,plain,(
    ! [A_65] :
      ( m1_subset_1(A_65,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_65,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_152])).

tff(c_56,plain,(
    v1_yellow_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_24,plain,(
    ! [A_19] :
      ( r1_yellow_0(A_19,k1_xboole_0)
      | ~ l1_orders_2(A_19)
      | ~ v1_yellow_0(A_19)
      | ~ v5_orders_2(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    ! [A_56] :
      ( k1_yellow_0(A_56,k1_xboole_0) = k3_yellow_0(A_56)
      | ~ l1_orders_2(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_93,plain,(
    k1_yellow_0('#skF_4',k1_xboole_0) = k3_yellow_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_89])).

tff(c_28160,plain,(
    ! [A_1687,B_1688,C_1689] :
      ( r1_orders_2(A_1687,k1_yellow_0(A_1687,B_1688),k1_yellow_0(A_1687,C_1689))
      | ~ r1_yellow_0(A_1687,C_1689)
      | ~ r1_yellow_0(A_1687,B_1688)
      | ~ r1_tarski(B_1688,C_1689)
      | ~ l1_orders_2(A_1687) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28163,plain,(
    ! [C_1689] :
      ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),k1_yellow_0('#skF_4',C_1689))
      | ~ r1_yellow_0('#skF_4',C_1689)
      | ~ r1_yellow_0('#skF_4',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,C_1689)
      | ~ l1_orders_2('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_28160])).

tff(c_28168,plain,(
    ! [C_1689] :
      ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),k1_yellow_0('#skF_4',C_1689))
      | ~ r1_yellow_0('#skF_4',C_1689)
      | ~ r1_yellow_0('#skF_4',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2,c_28163])).

tff(c_28171,plain,(
    ~ r1_yellow_0('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_28168])).

tff(c_28174,plain,
    ( ~ l1_orders_2('#skF_4')
    | ~ v1_yellow_0('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_28171])).

tff(c_28177,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_28174])).

tff(c_28179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_28177])).

tff(c_28180,plain,(
    ! [C_1689] :
      ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),k1_yellow_0('#skF_4',C_1689))
      | ~ r1_yellow_0('#skF_4',C_1689) ) ),
    inference(splitRight,[status(thm)],[c_28168])).

tff(c_28322,plain,(
    ! [D_1705,B_1706,A_1707,C_1708] :
      ( r2_hidden(D_1705,B_1706)
      | ~ r1_orders_2(A_1707,C_1708,D_1705)
      | ~ r2_hidden(C_1708,B_1706)
      | ~ m1_subset_1(D_1705,u1_struct_0(A_1707))
      | ~ m1_subset_1(C_1708,u1_struct_0(A_1707))
      | ~ v13_waybel_0(B_1706,A_1707)
      | ~ m1_subset_1(B_1706,k1_zfmisc_1(u1_struct_0(A_1707)))
      | ~ l1_orders_2(A_1707) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_28334,plain,(
    ! [C_1689,B_1706] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_1689),B_1706)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1706)
      | ~ m1_subset_1(k1_yellow_0('#skF_4',C_1689),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1706,'#skF_4')
      | ~ m1_subset_1(B_1706,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ r1_yellow_0('#skF_4',C_1689) ) ),
    inference(resolution,[status(thm)],[c_28180,c_28322])).

tff(c_28356,plain,(
    ! [C_1689,B_1706] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_1689),B_1706)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1706)
      | ~ m1_subset_1(k1_yellow_0('#skF_4',C_1689),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1706,'#skF_4')
      | ~ m1_subset_1(B_1706,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',C_1689) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_28334])).

tff(c_28645,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_28356])).

tff(c_28654,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_157,c_28645])).

tff(c_28661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_28654])).

tff(c_28777,plain,(
    ! [C_1725,B_1726] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_1725),B_1726)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1726)
      | ~ m1_subset_1(k1_yellow_0('#skF_4',C_1725),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1726,'#skF_4')
      | ~ m1_subset_1(B_1726,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',C_1725) ) ),
    inference(splitRight,[status(thm)],[c_28356])).

tff(c_28782,plain,(
    ! [B_5,B_1726] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5))),B_1726)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1726)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1726,'#skF_4')
      | ~ m1_subset_1(B_1726,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28211,c_28777])).

tff(c_28802,plain,(
    ! [B_5,B_1726] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5))),B_1726)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1726)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1726,'#skF_4')
      | ~ m1_subset_1(B_1726,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_28782])).

tff(c_32845,plain,(
    ! [B_1922,B_1923] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_1922))),B_1923)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1923)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1922),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1923,'#skF_4')
      | ~ m1_subset_1(B_1923,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_1922)))
      | u1_struct_0('#skF_4') = B_1922
      | ~ m1_subset_1(B_1922,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_28802])).

tff(c_32880,plain,(
    ! [B_5,B_1923] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),B_1923)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1923)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1923,'#skF_4')
      | ~ m1_subset_1(B_1923,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28211,c_32845])).

tff(c_32903,plain,(
    ! [B_5,B_1923] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),B_1923)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1923)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1923,'#skF_4')
      | ~ m1_subset_1(B_1923,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_32880])).

tff(c_32905,plain,(
    ! [B_1924,B_1925] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1924),B_1925)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1925)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1924),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1925,'#skF_4')
      | ~ m1_subset_1(B_1925,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_1924)))
      | u1_struct_0('#skF_4') = B_1924
      | ~ m1_subset_1(B_1924,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_32903])).

tff(c_32908,plain,(
    ! [B_1924,B_1925] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1924),B_1925)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1925)
      | ~ v13_waybel_0(B_1925,'#skF_4')
      | ~ m1_subset_1(B_1925,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_1924
      | ~ m1_subset_1(B_1924,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1924),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_32905])).

tff(c_32911,plain,(
    ! [B_1924,B_1925] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1924),B_1925)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1925)
      | ~ v13_waybel_0(B_1925,'#skF_4')
      | ~ m1_subset_1(B_1925,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_1924
      | ~ m1_subset_1(B_1924,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1924),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_32908])).

tff(c_32913,plain,(
    ! [B_1926,B_1927] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1926),B_1927)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1927)
      | ~ v13_waybel_0(B_1927,'#skF_4')
      | ~ m1_subset_1(B_1927,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_1926
      | ~ m1_subset_1(B_1926,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1926),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_32911])).

tff(c_32922,plain,(
    ! [B_1928,B_1929] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1928),B_1929)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1929)
      | ~ v13_waybel_0(B_1929,'#skF_4')
      | ~ m1_subset_1(B_1929,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_1928
      | ~ m1_subset_1(B_1928,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_32913])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( ~ r2_hidden('#skF_1'(A_4,B_5),B_5)
      | B_5 = A_4
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32963,plain,(
    ! [B_1930] :
      ( ~ r2_hidden(k3_yellow_0('#skF_4'),B_1930)
      | ~ v13_waybel_0(B_1930,'#skF_4')
      | u1_struct_0('#skF_4') = B_1930
      | ~ m1_subset_1(B_1930,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_32922,c_8])).

tff(c_32970,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v13_waybel_0('#skF_5','#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_32963])).

tff(c_32978,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_134,c_32970])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_290,plain,(
    ! [A_103,B_104] :
      ( k1_yellow_0(A_103,k5_waybel_0(A_103,B_104)) = B_104
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_307,plain,(
    ! [A_103,B_5] :
      ( k1_yellow_0(A_103,k5_waybel_0(A_103,'#skF_1'(u1_struct_0(A_103),B_5))) = '#skF_1'(u1_struct_0(A_103),B_5)
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103)
      | u1_struct_0(A_103) = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_103))) ) ),
    inference(resolution,[status(thm)],[c_10,c_290])).

tff(c_268,plain,(
    ! [A_100,B_101,C_102] :
      ( r1_orders_2(A_100,k1_yellow_0(A_100,B_101),k1_yellow_0(A_100,C_102))
      | ~ r1_yellow_0(A_100,C_102)
      | ~ r1_yellow_0(A_100,B_101)
      | ~ r1_tarski(B_101,C_102)
      | ~ l1_orders_2(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_271,plain,(
    ! [C_102] :
      ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),k1_yellow_0('#skF_4',C_102))
      | ~ r1_yellow_0('#skF_4',C_102)
      | ~ r1_yellow_0('#skF_4',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,C_102)
      | ~ l1_orders_2('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_268])).

tff(c_276,plain,(
    ! [C_102] :
      ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),k1_yellow_0('#skF_4',C_102))
      | ~ r1_yellow_0('#skF_4',C_102)
      | ~ r1_yellow_0('#skF_4',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2,c_271])).

tff(c_279,plain,(
    ~ r1_yellow_0('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_282,plain,
    ( ~ l1_orders_2('#skF_4')
    | ~ v1_yellow_0('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_279])).

tff(c_285,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_282])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_285])).

tff(c_289,plain,(
    r1_yellow_0('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_288,plain,(
    ! [C_102] :
      ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),k1_yellow_0('#skF_4',C_102))
      | ~ r1_yellow_0('#skF_4',C_102) ) ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_400,plain,(
    ! [D_113,B_114,A_115,C_116] :
      ( r2_hidden(D_113,B_114)
      | ~ r1_orders_2(A_115,C_116,D_113)
      | ~ r2_hidden(C_116,B_114)
      | ~ m1_subset_1(D_113,u1_struct_0(A_115))
      | ~ m1_subset_1(C_116,u1_struct_0(A_115))
      | ~ v13_waybel_0(B_114,A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_orders_2(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_410,plain,(
    ! [C_102,B_114] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_102),B_114)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_114)
      | ~ m1_subset_1(k1_yellow_0('#skF_4',C_102),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_114,'#skF_4')
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ r1_yellow_0('#skF_4',C_102) ) ),
    inference(resolution,[status(thm)],[c_288,c_400])).

tff(c_429,plain,(
    ! [C_102,B_114] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_102),B_114)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_114)
      | ~ m1_subset_1(k1_yellow_0('#skF_4',C_102),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_114,'#skF_4')
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',C_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_410])).

tff(c_750,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_429])).

tff(c_753,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_157,c_750])).

tff(c_760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_753])).

tff(c_885,plain,(
    ! [C_139,B_140] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_139),B_140)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_140)
      | ~ m1_subset_1(k1_yellow_0('#skF_4',C_139),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_140,'#skF_4')
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',C_139) ) ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_890,plain,(
    ! [B_5,B_140] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5))),B_140)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_140)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_140,'#skF_4')
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_885])).

tff(c_910,plain,(
    ! [B_5,B_140] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5))),B_140)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_140)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_140,'#skF_4')
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_890])).

tff(c_6049,plain,(
    ! [B_448,B_449] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_448))),B_449)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_449)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_448),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_449,'#skF_4')
      | ~ m1_subset_1(B_449,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_448)))
      | u1_struct_0('#skF_4') = B_448
      | ~ m1_subset_1(B_448,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_910])).

tff(c_6084,plain,(
    ! [B_5,B_449] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),B_449)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_449)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_449,'#skF_4')
      | ~ m1_subset_1(B_449,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_6049])).

tff(c_6107,plain,(
    ! [B_5,B_449] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),B_449)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_449)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_449,'#skF_4')
      | ~ m1_subset_1(B_449,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_6084])).

tff(c_6109,plain,(
    ! [B_450,B_451] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_450),B_451)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_451)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_450),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_451,'#skF_4')
      | ~ m1_subset_1(B_451,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_450)))
      | u1_struct_0('#skF_4') = B_450
      | ~ m1_subset_1(B_450,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6107])).

tff(c_6112,plain,(
    ! [B_450,B_451] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_450),B_451)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_451)
      | ~ v13_waybel_0(B_451,'#skF_4')
      | ~ m1_subset_1(B_451,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_450
      | ~ m1_subset_1(B_450,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_450),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_6109])).

tff(c_6115,plain,(
    ! [B_450,B_451] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_450),B_451)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_451)
      | ~ v13_waybel_0(B_451,'#skF_4')
      | ~ m1_subset_1(B_451,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_450
      | ~ m1_subset_1(B_450,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_450),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_6112])).

tff(c_6117,plain,(
    ! [B_452,B_453] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_452),B_453)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_453)
      | ~ v13_waybel_0(B_453,'#skF_4')
      | ~ m1_subset_1(B_453,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_452
      | ~ m1_subset_1(B_452,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_452),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6115])).

tff(c_6126,plain,(
    ! [B_454,B_455] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_454),B_455)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_455)
      | ~ v13_waybel_0(B_455,'#skF_4')
      | ~ m1_subset_1(B_455,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_454
      | ~ m1_subset_1(B_454,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_6117])).

tff(c_6167,plain,(
    ! [B_456] :
      ( ~ r2_hidden(k3_yellow_0('#skF_4'),B_456)
      | ~ v13_waybel_0(B_456,'#skF_4')
      | u1_struct_0('#skF_4') = B_456
      | ~ m1_subset_1(B_456,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_6126,c_8])).

tff(c_6174,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v13_waybel_0('#skF_5','#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_6167])).

tff(c_6182,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_134,c_6174])).

tff(c_301,plain,(
    ! [A_65] :
      ( k1_yellow_0('#skF_4',k5_waybel_0('#skF_4',A_65)) = A_65
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(A_65,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_157,c_290])).

tff(c_310,plain,(
    ! [A_65] :
      ( k1_yellow_0('#skF_4',k5_waybel_0('#skF_4',A_65)) = A_65
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(A_65,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_301])).

tff(c_311,plain,(
    ! [A_65] :
      ( k1_yellow_0('#skF_4',k5_waybel_0('#skF_4',A_65)) = A_65
      | ~ r2_hidden(A_65,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_310])).

tff(c_2164,plain,(
    ! [B_255,B_256] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_255))),B_256)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_256)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_255),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_256,'#skF_4')
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_255)))
      | u1_struct_0('#skF_4') = B_255
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_910])).

tff(c_2191,plain,(
    ! [B_5,B_256] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),B_256)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_256)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_256,'#skF_4')
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_2164])).

tff(c_2208,plain,(
    ! [B_5,B_256] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),B_256)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_256)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_256,'#skF_4')
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_2191])).

tff(c_2211,plain,(
    ! [B_258,B_259] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_258),B_259)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_259)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_258),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_259,'#skF_4')
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_258)))
      | u1_struct_0('#skF_4') = B_258
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2208])).

tff(c_2214,plain,(
    ! [B_258,B_259] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_258),B_259)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_259)
      | ~ v13_waybel_0(B_259,'#skF_4')
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_258
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_258),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_2211])).

tff(c_2217,plain,(
    ! [B_258,B_259] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_258),B_259)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_259)
      | ~ v13_waybel_0(B_259,'#skF_4')
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_258
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_258),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_2214])).

tff(c_2219,plain,(
    ! [B_260,B_261] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_260),B_261)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_261)
      | ~ v13_waybel_0(B_261,'#skF_4')
      | ~ m1_subset_1(B_261,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_260
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_260),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2217])).

tff(c_2228,plain,(
    ! [B_262,B_263] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_262),B_263)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_263)
      | ~ v13_waybel_0(B_263,'#skF_4')
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_262
      | ~ m1_subset_1(B_262,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_2219])).

tff(c_2255,plain,(
    ! [B_264] :
      ( ~ r2_hidden(k3_yellow_0('#skF_4'),B_264)
      | ~ v13_waybel_0(B_264,'#skF_4')
      | u1_struct_0('#skF_4') = B_264
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2228,c_8])).

tff(c_2262,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v13_waybel_0('#skF_5','#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_2255])).

tff(c_2270,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_134,c_2262])).

tff(c_36,plain,(
    ! [A_20,B_34] :
      ( m1_subset_1('#skF_2'(A_20,B_34),u1_struct_0(A_20))
      | v13_waybel_0(B_34,A_20)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_207,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_2'(A_81,B_82),B_82)
      | v13_waybel_0(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_orders_2(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_221,plain,(
    ! [A_83] :
      ( r2_hidden('#skF_2'(A_83,u1_struct_0(A_83)),u1_struct_0(A_83))
      | v13_waybel_0(u1_struct_0(A_83),A_83)
      | ~ l1_orders_2(A_83) ) ),
    inference(resolution,[status(thm)],[c_73,c_207])).

tff(c_158,plain,(
    ! [A_65,A_3] :
      ( m1_subset_1(A_65,A_3)
      | ~ r2_hidden(A_65,A_3) ) ),
    inference(resolution,[status(thm)],[c_73,c_152])).

tff(c_225,plain,(
    ! [A_83] :
      ( m1_subset_1('#skF_2'(A_83,u1_struct_0(A_83)),u1_struct_0(A_83))
      | v13_waybel_0(u1_struct_0(A_83),A_83)
      | ~ l1_orders_2(A_83) ) ),
    inference(resolution,[status(thm)],[c_221,c_158])).

tff(c_505,plain,(
    ! [A_125] :
      ( k1_yellow_0(A_125,k5_waybel_0(A_125,'#skF_2'(A_125,u1_struct_0(A_125)))) = '#skF_2'(A_125,u1_struct_0(A_125))
      | ~ v5_orders_2(A_125)
      | ~ v4_orders_2(A_125)
      | ~ v3_orders_2(A_125)
      | v2_struct_0(A_125)
      | v13_waybel_0(u1_struct_0(A_125),A_125)
      | ~ l1_orders_2(A_125) ) ),
    inference(resolution,[status(thm)],[c_225,c_290])).

tff(c_524,plain,
    ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),'#skF_2'('#skF_4',u1_struct_0('#skF_4')))
    | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_2'('#skF_4',u1_struct_0('#skF_4'))))
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | v13_waybel_0(u1_struct_0('#skF_4'),'#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_288])).

tff(c_553,plain,
    ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),'#skF_2'('#skF_4',u1_struct_0('#skF_4')))
    | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_2'('#skF_4',u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_4')
    | v13_waybel_0(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_62,c_60,c_58,c_524])).

tff(c_554,plain,
    ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),'#skF_2'('#skF_4',u1_struct_0('#skF_4')))
    | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_2'('#skF_4',u1_struct_0('#skF_4'))))
    | v13_waybel_0(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_553])).

tff(c_579,plain,(
    ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_2'('#skF_4',u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_554])).

tff(c_582,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4',u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_579])).

tff(c_585,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4',u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_582])).

tff(c_586,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4',u1_struct_0('#skF_4')),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_585])).

tff(c_589,plain,
    ( v13_waybel_0(u1_struct_0('#skF_4'),'#skF_4')
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_586])).

tff(c_598,plain,(
    v13_waybel_0(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_73,c_589])).

tff(c_924,plain,(
    ! [C_141,B_142] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_141),B_142)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_142)
      | ~ v13_waybel_0(B_142,'#skF_4')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',C_141)
      | ~ r2_hidden(k1_yellow_0('#skF_4',C_141),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_157,c_885])).

tff(c_932,plain,(
    ! [C_141] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_141),u1_struct_0('#skF_4'))
      | ~ r2_hidden(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(u1_struct_0('#skF_4'),'#skF_4')
      | ~ r1_yellow_0('#skF_4',C_141)
      | ~ r2_hidden(k1_yellow_0('#skF_4',C_141),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_73,c_924])).

tff(c_939,plain,(
    ! [C_141] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_141),u1_struct_0('#skF_4'))
      | ~ r2_hidden(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ r1_yellow_0('#skF_4',C_141)
      | ~ r2_hidden(k1_yellow_0('#skF_4',C_141),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_932])).

tff(c_940,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_939])).

tff(c_2446,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2270,c_940])).

tff(c_2463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_2446])).

tff(c_2471,plain,(
    ! [C_267] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_267),u1_struct_0('#skF_4'))
      | ~ r1_yellow_0('#skF_4',C_267)
      | ~ r2_hidden(k1_yellow_0('#skF_4',C_267),'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_939])).

tff(c_2523,plain,(
    ! [A_269] :
      ( r2_hidden(A_269,u1_struct_0('#skF_4'))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4',A_269))
      | ~ r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4',A_269)),'#skF_5')
      | ~ r2_hidden(A_269,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_2471])).

tff(c_2566,plain,(
    ! [A_270] :
      ( r2_hidden(A_270,u1_struct_0('#skF_4'))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4',A_270))
      | ~ r2_hidden(A_270,'#skF_5')
      | ~ r2_hidden(A_270,'#skF_5')
      | ~ r2_hidden(A_270,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_2523])).

tff(c_2631,plain,(
    ! [A_273] :
      ( u1_struct_0('#skF_4') = A_273
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_273))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(A_273,u1_struct_0('#skF_4'))))
      | ~ r2_hidden('#skF_1'(A_273,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2566,c_8])).

tff(c_2634,plain,(
    ! [A_273] :
      ( u1_struct_0('#skF_4') = A_273
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_273))
      | ~ r2_hidden('#skF_1'(A_273,u1_struct_0('#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_273,u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_2631])).

tff(c_2637,plain,(
    ! [A_273] :
      ( u1_struct_0('#skF_4') = A_273
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_273))
      | ~ r2_hidden('#skF_1'(A_273,u1_struct_0('#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_273,u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_2634])).

tff(c_2649,plain,(
    ! [A_277] :
      ( u1_struct_0('#skF_4') = A_277
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_277))
      | ~ r2_hidden('#skF_1'(A_277,u1_struct_0('#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_277,u1_struct_0('#skF_4')),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2637])).

tff(c_2662,plain,(
    ! [A_278] :
      ( u1_struct_0('#skF_4') = A_278
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_278))
      | ~ r2_hidden('#skF_1'(A_278,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_157,c_2649])).

tff(c_2665,plain,(
    ! [A_278] :
      ( u1_struct_0('#skF_4') = A_278
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_278))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1('#skF_1'(A_278,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_2662])).

tff(c_2669,plain,(
    ! [A_279] :
      ( u1_struct_0('#skF_4') = A_279
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_279))
      | ~ m1_subset_1('#skF_1'(A_279,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2665])).

tff(c_2674,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10,c_2669])).

tff(c_2688,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2674])).

tff(c_6258,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6182,c_2688])).

tff(c_6284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_6258])).

tff(c_6285,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2674])).

tff(c_169,plain,(
    ! [A_71,B_72] :
      ( ~ r2_hidden('#skF_1'(A_71,B_72),B_72)
      | B_72 = A_71
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_187,plain,(
    ! [B_77,A_78] :
      ( B_77 = A_78
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_78))
      | v1_xboole_0(B_77)
      | ~ m1_subset_1('#skF_1'(A_78,B_77),B_77) ) ),
    inference(resolution,[status(thm)],[c_12,c_169])).

tff(c_200,plain,(
    ! [A_78] :
      ( u1_struct_0('#skF_4') = A_78
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_78))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_78,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_157,c_187])).

tff(c_206,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_6344,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6285,c_206])).

tff(c_6352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_6344])).

tff(c_6353,plain,
    ( v13_waybel_0(u1_struct_0('#skF_4'),'#skF_4')
    | r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),'#skF_2'('#skF_4',u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_554])).

tff(c_6355,plain,(
    r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),'#skF_2'('#skF_4',u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_6353])).

tff(c_26,plain,(
    ! [D_43,B_34,A_20,C_41] :
      ( r2_hidden(D_43,B_34)
      | ~ r1_orders_2(A_20,C_41,D_43)
      | ~ r2_hidden(C_41,B_34)
      | ~ m1_subset_1(D_43,u1_struct_0(A_20))
      | ~ m1_subset_1(C_41,u1_struct_0(A_20))
      | ~ v13_waybel_0(B_34,A_20)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6360,plain,(
    ! [B_34] :
      ( r2_hidden('#skF_2'('#skF_4',u1_struct_0('#skF_4')),B_34)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_34)
      | ~ m1_subset_1('#skF_2'('#skF_4',u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_34,'#skF_4')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6355,c_26])).

tff(c_6363,plain,(
    ! [B_34] :
      ( r2_hidden('#skF_2'('#skF_4',u1_struct_0('#skF_4')),B_34)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_34)
      | ~ m1_subset_1('#skF_2'('#skF_4',u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_34,'#skF_4')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6360])).

tff(c_6542,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6363])).

tff(c_6551,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_157,c_6542])).

tff(c_6558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_6551])).

tff(c_6560,plain,(
    m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6363])).

tff(c_6715,plain,(
    ! [C_479,B_480] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_479),B_480)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_480)
      | ~ m1_subset_1(k1_yellow_0('#skF_4',C_479),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_480,'#skF_4')
      | ~ m1_subset_1(B_480,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',C_479) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6560,c_429])).

tff(c_6723,plain,(
    ! [B_5,B_480] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5))),B_480)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_480)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_480,'#skF_4')
      | ~ m1_subset_1(B_480,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_6715])).

tff(c_6743,plain,(
    ! [B_5,B_480] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5))),B_480)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_480)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_480,'#skF_4')
      | ~ m1_subset_1(B_480,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_6723])).

tff(c_11416,plain,(
    ! [B_751,B_752] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_751))),B_752)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_752)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_751),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_752,'#skF_4')
      | ~ m1_subset_1(B_752,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_751)))
      | u1_struct_0('#skF_4') = B_751
      | ~ m1_subset_1(B_751,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6743])).

tff(c_11451,plain,(
    ! [B_5,B_752] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),B_752)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_752)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_752,'#skF_4')
      | ~ m1_subset_1(B_752,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_11416])).

tff(c_11474,plain,(
    ! [B_5,B_752] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),B_752)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_752)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_752,'#skF_4')
      | ~ m1_subset_1(B_752,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_11451])).

tff(c_11476,plain,(
    ! [B_753,B_754] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_753),B_754)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_754)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_753),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_754,'#skF_4')
      | ~ m1_subset_1(B_754,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_753)))
      | u1_struct_0('#skF_4') = B_753
      | ~ m1_subset_1(B_753,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11474])).

tff(c_11479,plain,(
    ! [B_753,B_754] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_753),B_754)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_754)
      | ~ v13_waybel_0(B_754,'#skF_4')
      | ~ m1_subset_1(B_754,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_753
      | ~ m1_subset_1(B_753,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_753),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_11476])).

tff(c_11482,plain,(
    ! [B_753,B_754] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_753),B_754)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_754)
      | ~ v13_waybel_0(B_754,'#skF_4')
      | ~ m1_subset_1(B_754,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_753
      | ~ m1_subset_1(B_753,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_753),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_11479])).

tff(c_11484,plain,(
    ! [B_755,B_756] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_755),B_756)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_756)
      | ~ v13_waybel_0(B_756,'#skF_4')
      | ~ m1_subset_1(B_756,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_755
      | ~ m1_subset_1(B_755,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_755),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11482])).

tff(c_11493,plain,(
    ! [B_757,B_758] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_757),B_758)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_758)
      | ~ v13_waybel_0(B_758,'#skF_4')
      | ~ m1_subset_1(B_758,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_757
      | ~ m1_subset_1(B_757,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_11484])).

tff(c_11528,plain,(
    ! [B_759] :
      ( ~ r2_hidden(k3_yellow_0('#skF_4'),B_759)
      | ~ v13_waybel_0(B_759,'#skF_4')
      | u1_struct_0('#skF_4') = B_759
      | ~ m1_subset_1(B_759,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_11493,c_8])).

tff(c_11535,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v13_waybel_0('#skF_5','#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_11528])).

tff(c_11543,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_134,c_11535])).

tff(c_7864,plain,(
    ! [B_579,B_580] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_579))),B_580)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_580)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_579),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_580,'#skF_4')
      | ~ m1_subset_1(B_580,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_579)))
      | u1_struct_0('#skF_4') = B_579
      | ~ m1_subset_1(B_579,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6743])).

tff(c_7887,plain,(
    ! [B_5,B_580] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),B_580)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_580)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_580,'#skF_4')
      | ~ m1_subset_1(B_580,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_7864])).

tff(c_7902,plain,(
    ! [B_5,B_580] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),B_580)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_580)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_580,'#skF_4')
      | ~ m1_subset_1(B_580,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_7887])).

tff(c_7904,plain,(
    ! [B_581,B_582] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_581),B_582)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_582)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_581),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_582,'#skF_4')
      | ~ m1_subset_1(B_582,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_581)))
      | u1_struct_0('#skF_4') = B_581
      | ~ m1_subset_1(B_581,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_7902])).

tff(c_7907,plain,(
    ! [B_581,B_582] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_581),B_582)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_582)
      | ~ v13_waybel_0(B_582,'#skF_4')
      | ~ m1_subset_1(B_582,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_581
      | ~ m1_subset_1(B_581,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_581),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_7904])).

tff(c_7910,plain,(
    ! [B_581,B_582] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_581),B_582)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_582)
      | ~ v13_waybel_0(B_582,'#skF_4')
      | ~ m1_subset_1(B_582,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_581
      | ~ m1_subset_1(B_581,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_581),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_7907])).

tff(c_7912,plain,(
    ! [B_583,B_584] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_583),B_584)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_584)
      | ~ v13_waybel_0(B_584,'#skF_4')
      | ~ m1_subset_1(B_584,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_583
      | ~ m1_subset_1(B_583,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_583),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_7910])).

tff(c_7921,plain,(
    ! [B_585,B_586] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_585),B_586)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_586)
      | ~ v13_waybel_0(B_586,'#skF_4')
      | ~ m1_subset_1(B_586,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_585
      | ~ m1_subset_1(B_585,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_7912])).

tff(c_7945,plain,(
    ! [B_587] :
      ( ~ r2_hidden(k3_yellow_0('#skF_4'),B_587)
      | ~ v13_waybel_0(B_587,'#skF_4')
      | u1_struct_0('#skF_4') = B_587
      | ~ m1_subset_1(B_587,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_7921,c_8])).

tff(c_7952,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v13_waybel_0('#skF_5','#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_7945])).

tff(c_7960,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_134,c_7952])).

tff(c_34,plain,(
    ! [A_20,B_34] :
      ( m1_subset_1('#skF_3'(A_20,B_34),u1_struct_0(A_20))
      | v13_waybel_0(B_34,A_20)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6365,plain,(
    ! [A_463,B_464] :
      ( k1_yellow_0(A_463,k5_waybel_0(A_463,'#skF_3'(A_463,B_464))) = '#skF_3'(A_463,B_464)
      | ~ v5_orders_2(A_463)
      | ~ v4_orders_2(A_463)
      | ~ v3_orders_2(A_463)
      | v2_struct_0(A_463)
      | v13_waybel_0(B_464,A_463)
      | ~ m1_subset_1(B_464,k1_zfmisc_1(u1_struct_0(A_463)))
      | ~ l1_orders_2(A_463) ) ),
    inference(resolution,[status(thm)],[c_34,c_290])).

tff(c_6445,plain,(
    ! [A_468] :
      ( k1_yellow_0(A_468,k5_waybel_0(A_468,'#skF_3'(A_468,u1_struct_0(A_468)))) = '#skF_3'(A_468,u1_struct_0(A_468))
      | ~ v5_orders_2(A_468)
      | ~ v4_orders_2(A_468)
      | ~ v3_orders_2(A_468)
      | v2_struct_0(A_468)
      | v13_waybel_0(u1_struct_0(A_468),A_468)
      | ~ l1_orders_2(A_468) ) ),
    inference(resolution,[status(thm)],[c_73,c_6365])).

tff(c_6464,plain,
    ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),'#skF_3'('#skF_4',u1_struct_0('#skF_4')))
    | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_3'('#skF_4',u1_struct_0('#skF_4'))))
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | v13_waybel_0(u1_struct_0('#skF_4'),'#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6445,c_288])).

tff(c_6493,plain,
    ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),'#skF_3'('#skF_4',u1_struct_0('#skF_4')))
    | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_3'('#skF_4',u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_4')
    | v13_waybel_0(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_62,c_60,c_58,c_6464])).

tff(c_6494,plain,
    ( r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),'#skF_3'('#skF_4',u1_struct_0('#skF_4')))
    | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_3'('#skF_4',u1_struct_0('#skF_4'))))
    | v13_waybel_0(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6493])).

tff(c_6504,plain,(
    ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_3'('#skF_4',u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_6494])).

tff(c_6508,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_4',u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_6504])).

tff(c_6511,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_4',u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_6508])).

tff(c_6512,plain,(
    ~ m1_subset_1('#skF_3'('#skF_4',u1_struct_0('#skF_4')),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6511])).

tff(c_6515,plain,
    ( v13_waybel_0(u1_struct_0('#skF_4'),'#skF_4')
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_6512])).

tff(c_6521,plain,(
    v13_waybel_0(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_73,c_6515])).

tff(c_6754,plain,(
    ! [C_481,B_482] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_481),B_482)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_482)
      | ~ v13_waybel_0(B_482,'#skF_4')
      | ~ m1_subset_1(B_482,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',C_481)
      | ~ r2_hidden(k1_yellow_0('#skF_4',C_481),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_157,c_6715])).

tff(c_6762,plain,(
    ! [C_481] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_481),u1_struct_0('#skF_4'))
      | ~ r2_hidden(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(u1_struct_0('#skF_4'),'#skF_4')
      | ~ r1_yellow_0('#skF_4',C_481)
      | ~ r2_hidden(k1_yellow_0('#skF_4',C_481),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_73,c_6754])).

tff(c_6769,plain,(
    ! [C_481] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_481),u1_struct_0('#skF_4'))
      | ~ r2_hidden(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ r1_yellow_0('#skF_4',C_481)
      | ~ r2_hidden(k1_yellow_0('#skF_4',C_481),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6521,c_6762])).

tff(c_6770,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6769])).

tff(c_8000,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7960,c_6770])).

tff(c_8024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_8000])).

tff(c_8057,plain,(
    ! [C_592] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_592),u1_struct_0('#skF_4'))
      | ~ r1_yellow_0('#skF_4',C_592)
      | ~ r2_hidden(k1_yellow_0('#skF_4',C_592),'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_6769])).

tff(c_8108,plain,(
    ! [A_593] :
      ( r2_hidden(A_593,u1_struct_0('#skF_4'))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4',A_593))
      | ~ r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4',A_593)),'#skF_5')
      | ~ r2_hidden(A_593,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_8057])).

tff(c_8188,plain,(
    ! [A_595] :
      ( r2_hidden(A_595,u1_struct_0('#skF_4'))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4',A_595))
      | ~ r2_hidden(A_595,'#skF_5')
      | ~ r2_hidden(A_595,'#skF_5')
      | ~ r2_hidden(A_595,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_8108])).

tff(c_8224,plain,(
    ! [A_597] :
      ( u1_struct_0('#skF_4') = A_597
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_597))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(A_597,u1_struct_0('#skF_4'))))
      | ~ r2_hidden('#skF_1'(A_597,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8188,c_8])).

tff(c_8227,plain,(
    ! [A_597] :
      ( u1_struct_0('#skF_4') = A_597
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_597))
      | ~ r2_hidden('#skF_1'(A_597,u1_struct_0('#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_597,u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_8224])).

tff(c_8230,plain,(
    ! [A_597] :
      ( u1_struct_0('#skF_4') = A_597
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_597))
      | ~ r2_hidden('#skF_1'(A_597,u1_struct_0('#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_597,u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_8227])).

tff(c_8232,plain,(
    ! [A_598] :
      ( u1_struct_0('#skF_4') = A_598
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_598))
      | ~ r2_hidden('#skF_1'(A_598,u1_struct_0('#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_598,u1_struct_0('#skF_4')),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_8230])).

tff(c_8245,plain,(
    ! [A_599] :
      ( u1_struct_0('#skF_4') = A_599
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_599))
      | ~ r2_hidden('#skF_1'(A_599,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_157,c_8232])).

tff(c_8248,plain,(
    ! [A_599] :
      ( u1_struct_0('#skF_4') = A_599
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_599))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1('#skF_1'(A_599,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_8245])).

tff(c_8253,plain,(
    ! [A_602] :
      ( u1_struct_0('#skF_4') = A_602
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_602))
      | ~ m1_subset_1('#skF_1'(A_602,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_8248])).

tff(c_8258,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10,c_8253])).

tff(c_8259,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8258])).

tff(c_11617,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11543,c_8259])).

tff(c_11649,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_11617])).

tff(c_11650,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8258])).

tff(c_11695,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11650,c_206])).

tff(c_11703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_11695])).

tff(c_11704,plain,
    ( v13_waybel_0(u1_struct_0('#skF_4'),'#skF_4')
    | r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),'#skF_3'('#skF_4',u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_6494])).

tff(c_11706,plain,(
    r1_orders_2('#skF_4',k3_yellow_0('#skF_4'),'#skF_3'('#skF_4',u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_11704])).

tff(c_11711,plain,(
    ! [B_34] :
      ( r2_hidden('#skF_3'('#skF_4',u1_struct_0('#skF_4')),B_34)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_34)
      | ~ m1_subset_1('#skF_3'('#skF_4',u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_34,'#skF_4')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_11706,c_26])).

tff(c_11714,plain,(
    ! [B_34] :
      ( r2_hidden('#skF_3'('#skF_4',u1_struct_0('#skF_4')),B_34)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_34)
      | ~ m1_subset_1('#skF_3'('#skF_4',u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_34,'#skF_4')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_11711])).

tff(c_11715,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_11714])).

tff(c_11718,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_157,c_11715])).

tff(c_11725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_11718])).

tff(c_11727,plain,(
    m1_subset_1(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_11714])).

tff(c_20,plain,(
    ! [A_14,B_17,C_18] :
      ( r1_orders_2(A_14,k1_yellow_0(A_14,B_17),k1_yellow_0(A_14,C_18))
      | ~ r1_yellow_0(A_14,C_18)
      | ~ r1_yellow_0(A_14,B_17)
      | ~ r1_tarski(B_17,C_18)
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_17946,plain,(
    ! [A_1099,C_1100,B_1101,B_1102] :
      ( r2_hidden(k1_yellow_0(A_1099,C_1100),B_1101)
      | ~ r2_hidden(k1_yellow_0(A_1099,B_1102),B_1101)
      | ~ m1_subset_1(k1_yellow_0(A_1099,C_1100),u1_struct_0(A_1099))
      | ~ m1_subset_1(k1_yellow_0(A_1099,B_1102),u1_struct_0(A_1099))
      | ~ v13_waybel_0(B_1101,A_1099)
      | ~ m1_subset_1(B_1101,k1_zfmisc_1(u1_struct_0(A_1099)))
      | ~ r1_yellow_0(A_1099,C_1100)
      | ~ r1_yellow_0(A_1099,B_1102)
      | ~ r1_tarski(B_1102,C_1100)
      | ~ l1_orders_2(A_1099) ) ),
    inference(resolution,[status(thm)],[c_20,c_400])).

tff(c_17965,plain,(
    ! [C_1100,B_1101] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_1100),B_1101)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1101)
      | ~ m1_subset_1(k1_yellow_0('#skF_4',C_1100),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k1_yellow_0('#skF_4',k1_xboole_0),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1101,'#skF_4')
      | ~ m1_subset_1(B_1101,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',C_1100)
      | ~ r1_yellow_0('#skF_4',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,C_1100)
      | ~ l1_orders_2('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_17946])).

tff(c_17975,plain,(
    ! [C_1103,B_1104] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_1103),B_1104)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1104)
      | ~ m1_subset_1(k1_yellow_0('#skF_4',C_1103),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1104,'#skF_4')
      | ~ m1_subset_1(B_1104,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',C_1103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2,c_289,c_11727,c_93,c_17965])).

tff(c_17985,plain,(
    ! [B_5,B_1104] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5))),B_1104)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1104)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1104,'#skF_4')
      | ~ m1_subset_1(B_1104,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_17975])).

tff(c_18007,plain,(
    ! [B_5,B_1104] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5))),B_1104)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1104)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1104,'#skF_4')
      | ~ m1_subset_1(B_1104,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_17985])).

tff(c_27692,plain,(
    ! [B_1655,B_1656] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_1655))),B_1656)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1656)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1655),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1656,'#skF_4')
      | ~ m1_subset_1(B_1656,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_1655)))
      | u1_struct_0('#skF_4') = B_1655
      | ~ m1_subset_1(B_1655,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_18007])).

tff(c_27733,plain,(
    ! [B_5,B_1656] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),B_1656)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1656)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1656,'#skF_4')
      | ~ m1_subset_1(B_1656,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_27692])).

tff(c_27759,plain,(
    ! [B_5,B_1656] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),B_1656)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1656)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1656,'#skF_4')
      | ~ m1_subset_1(B_1656,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_27733])).

tff(c_27761,plain,(
    ! [B_1657,B_1658] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1657),B_1658)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1658)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1657),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1658,'#skF_4')
      | ~ m1_subset_1(B_1658,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_1657)))
      | u1_struct_0('#skF_4') = B_1657
      | ~ m1_subset_1(B_1657,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_27759])).

tff(c_27764,plain,(
    ! [B_1657,B_1658] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1657),B_1658)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1658)
      | ~ v13_waybel_0(B_1658,'#skF_4')
      | ~ m1_subset_1(B_1658,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_1657
      | ~ m1_subset_1(B_1657,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1657),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_27761])).

tff(c_27767,plain,(
    ! [B_1657,B_1658] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1657),B_1658)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1658)
      | ~ v13_waybel_0(B_1658,'#skF_4')
      | ~ m1_subset_1(B_1658,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_1657
      | ~ m1_subset_1(B_1657,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1657),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_27764])).

tff(c_27769,plain,(
    ! [B_1659,B_1660] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1659),B_1660)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1660)
      | ~ v13_waybel_0(B_1660,'#skF_4')
      | ~ m1_subset_1(B_1660,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_1659
      | ~ m1_subset_1(B_1659,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1659),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_27767])).

tff(c_27778,plain,(
    ! [B_1661,B_1662] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1661),B_1662)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1662)
      | ~ v13_waybel_0(B_1662,'#skF_4')
      | ~ m1_subset_1(B_1662,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_1661
      | ~ m1_subset_1(B_1661,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_27769])).

tff(c_27825,plain,(
    ! [B_1663] :
      ( ~ r2_hidden(k3_yellow_0('#skF_4'),B_1663)
      | ~ v13_waybel_0(B_1663,'#skF_4')
      | u1_struct_0('#skF_4') = B_1663
      | ~ m1_subset_1(B_1663,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_27778,c_8])).

tff(c_27832,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v13_waybel_0('#skF_5','#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_27825])).

tff(c_27840,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_134,c_27832])).

tff(c_22311,plain,(
    ! [B_1421,B_1422] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_1421))),B_1422)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1422)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1421),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1422,'#skF_4')
      | ~ m1_subset_1(B_1422,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_1421)))
      | u1_struct_0('#skF_4') = B_1421
      | ~ m1_subset_1(B_1421,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_18007])).

tff(c_22338,plain,(
    ! [B_5,B_1422] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),B_1422)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1422)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1422,'#skF_4')
      | ~ m1_subset_1(B_1422,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_22311])).

tff(c_22355,plain,(
    ! [B_5,B_1422] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),B_1422)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1422)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1422,'#skF_4')
      | ~ m1_subset_1(B_1422,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_22338])).

tff(c_22357,plain,(
    ! [B_1423,B_1424] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1423),B_1424)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1424)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1423),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1424,'#skF_4')
      | ~ m1_subset_1(B_1424,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_1423)))
      | u1_struct_0('#skF_4') = B_1423
      | ~ m1_subset_1(B_1423,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_22355])).

tff(c_22360,plain,(
    ! [B_1423,B_1424] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1423),B_1424)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1424)
      | ~ v13_waybel_0(B_1424,'#skF_4')
      | ~ m1_subset_1(B_1424,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_1423
      | ~ m1_subset_1(B_1423,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1423),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_22357])).

tff(c_22363,plain,(
    ! [B_1423,B_1424] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1423),B_1424)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1424)
      | ~ v13_waybel_0(B_1424,'#skF_4')
      | ~ m1_subset_1(B_1424,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_1423
      | ~ m1_subset_1(B_1423,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1423),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_22360])).

tff(c_22365,plain,(
    ! [B_1425,B_1426] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1425),B_1426)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1426)
      | ~ v13_waybel_0(B_1426,'#skF_4')
      | ~ m1_subset_1(B_1426,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_1425
      | ~ m1_subset_1(B_1425,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1425),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_22363])).

tff(c_22374,plain,(
    ! [B_1427,B_1428] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1427),B_1428)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1428)
      | ~ v13_waybel_0(B_1428,'#skF_4')
      | ~ m1_subset_1(B_1428,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_1427
      | ~ m1_subset_1(B_1427,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_22365])).

tff(c_22398,plain,(
    ! [B_1429] :
      ( ~ r2_hidden(k3_yellow_0('#skF_4'),B_1429)
      | ~ v13_waybel_0(B_1429,'#skF_4')
      | u1_struct_0('#skF_4') = B_1429
      | ~ m1_subset_1(B_1429,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_22374,c_8])).

tff(c_22405,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v13_waybel_0('#skF_5','#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_22398])).

tff(c_22413,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_134,c_22405])).

tff(c_20376,plain,(
    ! [B_1278,B_1279] :
      ( r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_1278))),B_1279)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1279)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1278),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1279,'#skF_4')
      | ~ m1_subset_1(B_1279,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_1278)))
      | u1_struct_0('#skF_4') = B_1278
      | ~ m1_subset_1(B_1278,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_18007])).

tff(c_20403,plain,(
    ! [B_5,B_1279] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),B_1279)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1279)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1279,'#skF_4')
      | ~ m1_subset_1(B_1279,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_20376])).

tff(c_20420,plain,(
    ! [B_5,B_1279] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_5),B_1279)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1279)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_5),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1279,'#skF_4')
      | ~ m1_subset_1(B_1279,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_5)))
      | v2_struct_0('#skF_4')
      | u1_struct_0('#skF_4') = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_20403])).

tff(c_20422,plain,(
    ! [B_1280,B_1281] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1280),B_1281)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1281)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1280),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(B_1281,'#skF_4')
      | ~ m1_subset_1(B_1281,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(u1_struct_0('#skF_4'),B_1280)))
      | u1_struct_0('#skF_4') = B_1280
      | ~ m1_subset_1(B_1280,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_20420])).

tff(c_20425,plain,(
    ! [B_1280,B_1281] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1280),B_1281)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1281)
      | ~ v13_waybel_0(B_1281,'#skF_4')
      | ~ m1_subset_1(B_1281,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_1280
      | ~ m1_subset_1(B_1280,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1280),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_20422])).

tff(c_20428,plain,(
    ! [B_1280,B_1281] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1280),B_1281)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1281)
      | ~ v13_waybel_0(B_1281,'#skF_4')
      | ~ m1_subset_1(B_1281,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_1280
      | ~ m1_subset_1(B_1280,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1280),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_20425])).

tff(c_20430,plain,(
    ! [B_1282,B_1283] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1282),B_1283)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1283)
      | ~ v13_waybel_0(B_1283,'#skF_4')
      | ~ m1_subset_1(B_1283,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_1282
      | ~ m1_subset_1(B_1282,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),B_1282),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_20428])).

tff(c_20439,plain,(
    ! [B_1284,B_1285] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_1284),B_1285)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1285)
      | ~ v13_waybel_0(B_1285,'#skF_4')
      | ~ m1_subset_1(B_1285,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | u1_struct_0('#skF_4') = B_1284
      | ~ m1_subset_1(B_1284,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_20430])).

tff(c_20469,plain,(
    ! [B_1286] :
      ( ~ r2_hidden(k3_yellow_0('#skF_4'),B_1286)
      | ~ v13_waybel_0(B_1286,'#skF_4')
      | u1_struct_0('#skF_4') = B_1286
      | ~ m1_subset_1(B_1286,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_20439,c_8])).

tff(c_20476,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v13_waybel_0('#skF_5','#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_20469])).

tff(c_20484,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_134,c_20476])).

tff(c_18018,plain,(
    ! [C_1105,B_1106] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_1105),B_1106)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_1106)
      | ~ v13_waybel_0(B_1106,'#skF_4')
      | ~ m1_subset_1(B_1106,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_yellow_0('#skF_4',C_1105)
      | ~ r2_hidden(k1_yellow_0('#skF_4',C_1105),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_157,c_17975])).

tff(c_18031,plain,(
    ! [C_1105] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_1105),u1_struct_0('#skF_4'))
      | ~ r2_hidden(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v13_waybel_0(u1_struct_0('#skF_4'),'#skF_4')
      | ~ r1_yellow_0('#skF_4',C_1105)
      | ~ r2_hidden(k1_yellow_0('#skF_4',C_1105),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_73,c_18018])).

tff(c_18032,plain,(
    ~ v13_waybel_0(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18031])).

tff(c_20568,plain,(
    ~ v13_waybel_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20484,c_18032])).

tff(c_20599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_20568])).

tff(c_20600,plain,(
    ! [C_1105] :
      ( ~ r2_hidden(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4'))
      | r2_hidden(k1_yellow_0('#skF_4',C_1105),u1_struct_0('#skF_4'))
      | ~ r1_yellow_0('#skF_4',C_1105)
      | ~ r2_hidden(k1_yellow_0('#skF_4',C_1105),'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_18031])).

tff(c_20606,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_20600])).

tff(c_22477,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22413,c_20606])).

tff(c_22509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_22477])).

tff(c_22518,plain,(
    ! [C_1432] :
      ( r2_hidden(k1_yellow_0('#skF_4',C_1432),u1_struct_0('#skF_4'))
      | ~ r1_yellow_0('#skF_4',C_1432)
      | ~ r2_hidden(k1_yellow_0('#skF_4',C_1432),'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_20600])).

tff(c_22603,plain,(
    ! [A_1433] :
      ( r2_hidden(A_1433,u1_struct_0('#skF_4'))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4',A_1433))
      | ~ r2_hidden(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4',A_1433)),'#skF_5')
      | ~ r2_hidden(A_1433,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_22518])).

tff(c_22651,plain,(
    ! [A_1434] :
      ( r2_hidden(A_1434,u1_struct_0('#skF_4'))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4',A_1434))
      | ~ r2_hidden(A_1434,'#skF_5')
      | ~ r2_hidden(A_1434,'#skF_5')
      | ~ r2_hidden(A_1434,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_22603])).

tff(c_22769,plain,(
    ! [A_1439] :
      ( u1_struct_0('#skF_4') = A_1439
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_1439))
      | ~ r1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_1'(A_1439,u1_struct_0('#skF_4'))))
      | ~ r2_hidden('#skF_1'(A_1439,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22651,c_8])).

tff(c_22772,plain,(
    ! [A_1439] :
      ( u1_struct_0('#skF_4') = A_1439
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_1439))
      | ~ r2_hidden('#skF_1'(A_1439,u1_struct_0('#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_1439,u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_22769])).

tff(c_22775,plain,(
    ! [A_1439] :
      ( u1_struct_0('#skF_4') = A_1439
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_1439))
      | ~ r2_hidden('#skF_1'(A_1439,u1_struct_0('#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_1439,u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_22772])).

tff(c_22777,plain,(
    ! [A_1440] :
      ( u1_struct_0('#skF_4') = A_1440
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_1440))
      | ~ r2_hidden('#skF_1'(A_1440,u1_struct_0('#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_1440,u1_struct_0('#skF_4')),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_22775])).

tff(c_22790,plain,(
    ! [A_1441] :
      ( u1_struct_0('#skF_4') = A_1441
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_1441))
      | ~ r2_hidden('#skF_1'(A_1441,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_157,c_22777])).

tff(c_22793,plain,(
    ! [A_1441] :
      ( u1_struct_0('#skF_4') = A_1441
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_1441))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1('#skF_1'(A_1441,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_22790])).

tff(c_22797,plain,(
    ! [A_1442] :
      ( u1_struct_0('#skF_4') = A_1442
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_1442))
      | ~ m1_subset_1('#skF_1'(A_1442,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_22793])).

tff(c_22802,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10,c_22797])).

tff(c_22803,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_22802])).

tff(c_27946,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27840,c_22803])).

tff(c_27988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_27946])).

tff(c_27989,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_22802])).

tff(c_28066,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27989,c_206])).

tff(c_28074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_28066])).

tff(c_28077,plain,(
    ! [A_1666] :
      ( u1_struct_0('#skF_4') = A_1666
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_1666))
      | ~ r2_hidden('#skF_1'(A_1666,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_28080,plain,(
    ! [A_1666] :
      ( u1_struct_0('#skF_4') = A_1666
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_1666))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1('#skF_1'(A_1666,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_28077])).

tff(c_28084,plain,(
    ! [A_1667] :
      ( u1_struct_0('#skF_4') = A_1667
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_1667))
      | ~ m1_subset_1('#skF_1'(A_1667,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_28080])).

tff(c_28089,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10,c_28084])).

tff(c_28090,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_28089])).

tff(c_33078,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32978,c_28090])).

tff(c_33090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_33078])).

tff(c_33091,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_28089])).

tff(c_135,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_33111,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33091,c_135])).

tff(c_33114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_33111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.56/8.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.65/9.03  
% 17.65/9.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.65/9.03  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 17.65/9.03  
% 17.65/9.03  %Foreground sorts:
% 17.65/9.03  
% 17.65/9.03  
% 17.65/9.03  %Background operators:
% 17.65/9.03  
% 17.65/9.03  
% 17.65/9.03  %Foreground operators:
% 17.65/9.03  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 17.65/9.03  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 17.65/9.03  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 17.65/9.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.65/9.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.65/9.03  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 17.65/9.03  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 17.65/9.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.65/9.03  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 17.65/9.03  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 17.65/9.03  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 17.65/9.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.65/9.03  tff('#skF_5', type, '#skF_5': $i).
% 17.65/9.03  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 17.65/9.03  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 17.65/9.03  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 17.65/9.03  tff(k5_waybel_0, type, k5_waybel_0: ($i * $i) > $i).
% 17.65/9.03  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 17.65/9.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.65/9.03  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 17.65/9.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.65/9.03  tff('#skF_4', type, '#skF_4': $i).
% 17.65/9.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.65/9.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.65/9.03  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 17.65/9.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 17.65/9.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.65/9.03  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 17.65/9.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.65/9.03  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 17.65/9.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.65/9.03  
% 17.83/9.07  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 17.83/9.07  tff(f_31, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 17.83/9.07  tff(f_128, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 17.83/9.07  tff(f_157, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 17.83/9.07  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 17.83/9.07  tff(f_60, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 17.83/9.07  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 17.83/9.07  tff(f_121, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r1_yellow_0(A, k5_waybel_0(A, B)) & (k1_yellow_0(A, k5_waybel_0(A, B)) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_waybel_0)).
% 17.83/9.07  tff(f_52, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 17.83/9.07  tff(f_84, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 17.83/9.07  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 17.83/9.07  tff(f_56, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 17.83/9.07  tff(f_71, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (((r1_tarski(B, C) & r1_yellow_0(A, B)) & r1_yellow_0(A, C)) => r1_orders_2(A, k1_yellow_0(A, B), k1_yellow_0(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_yellow_0)).
% 17.83/9.07  tff(f_103, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 17.83/9.07  tff(c_4, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 17.83/9.07  tff(c_6, plain, (![A_3]: (m1_subset_1(k2_subset_1(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.83/9.07  tff(c_73, plain, (![A_3]: (m1_subset_1(A_3, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 17.83/9.07  tff(c_44, plain, (![B_49]: (~v1_subset_1(B_49, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_128])).
% 17.83/9.07  tff(c_75, plain, (![B_49]: (~v1_subset_1(B_49, B_49))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_44])).
% 17.83/9.07  tff(c_48, plain, (v13_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.83/9.07  tff(c_52, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.83/9.07  tff(c_100, plain, (![A_57, B_58]: (r2_hidden(A_57, B_58) | v1_xboole_0(B_58) | ~m1_subset_1(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_46])).
% 17.83/9.07  tff(c_66, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.83/9.07  tff(c_98, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_66])).
% 17.83/9.07  tff(c_72, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.83/9.07  tff(c_99, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_98, c_72])).
% 17.83/9.07  tff(c_103, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_100, c_99])).
% 17.83/9.07  tff(c_106, plain, (~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_103])).
% 17.83/9.07  tff(c_54, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.83/9.07  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.83/9.07  tff(c_107, plain, (![B_59, A_60]: (v1_subset_1(B_59, A_60) | B_59=A_60 | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_128])).
% 17.83/9.07  tff(c_110, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_46, c_107])).
% 17.83/9.07  tff(c_116, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_98, c_110])).
% 17.83/9.07  tff(c_18, plain, (![A_13]: (m1_subset_1(k3_yellow_0(A_13), u1_struct_0(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 17.83/9.07  tff(c_127, plain, (m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5') | ~l1_orders_2('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_116, c_18])).
% 17.83/9.07  tff(c_131, plain, (m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_127])).
% 17.83/9.07  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_131])).
% 17.83/9.07  tff(c_134, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_66])).
% 17.83/9.07  tff(c_10, plain, (![A_4, B_5]: (m1_subset_1('#skF_1'(A_4, B_5), A_4) | B_5=A_4 | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 17.83/9.07  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.83/9.07  tff(c_62, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.83/9.07  tff(c_60, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.83/9.07  tff(c_58, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.83/9.07  tff(c_40, plain, (![A_45, B_47]: (r1_yellow_0(A_45, k5_waybel_0(A_45, B_47)) | ~m1_subset_1(B_47, u1_struct_0(A_45)) | ~l1_orders_2(A_45) | ~v5_orders_2(A_45) | ~v4_orders_2(A_45) | ~v3_orders_2(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.83/9.07  tff(c_28194, plain, (![A_1691, B_1692]: (k1_yellow_0(A_1691, k5_waybel_0(A_1691, B_1692))=B_1692 | ~m1_subset_1(B_1692, u1_struct_0(A_1691)) | ~l1_orders_2(A_1691) | ~v5_orders_2(A_1691) | ~v4_orders_2(A_1691) | ~v3_orders_2(A_1691) | v2_struct_0(A_1691))), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.83/9.07  tff(c_28211, plain, (![A_1691, B_5]: (k1_yellow_0(A_1691, k5_waybel_0(A_1691, '#skF_1'(u1_struct_0(A_1691), B_5)))='#skF_1'(u1_struct_0(A_1691), B_5) | ~l1_orders_2(A_1691) | ~v5_orders_2(A_1691) | ~v4_orders_2(A_1691) | ~v3_orders_2(A_1691) | v2_struct_0(A_1691) | u1_struct_0(A_1691)=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_1691))))), inference(resolution, [status(thm)], [c_10, c_28194])).
% 17.83/9.07  tff(c_152, plain, (![A_65, C_66, B_67]: (m1_subset_1(A_65, C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.83/9.07  tff(c_157, plain, (![A_65]: (m1_subset_1(A_65, u1_struct_0('#skF_4')) | ~r2_hidden(A_65, '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_152])).
% 17.83/9.07  tff(c_56, plain, (v1_yellow_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.83/9.07  tff(c_24, plain, (![A_19]: (r1_yellow_0(A_19, k1_xboole_0) | ~l1_orders_2(A_19) | ~v1_yellow_0(A_19) | ~v5_orders_2(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_84])).
% 17.83/9.07  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.83/9.07  tff(c_89, plain, (![A_56]: (k1_yellow_0(A_56, k1_xboole_0)=k3_yellow_0(A_56) | ~l1_orders_2(A_56))), inference(cnfTransformation, [status(thm)], [f_56])).
% 17.83/9.07  tff(c_93, plain, (k1_yellow_0('#skF_4', k1_xboole_0)=k3_yellow_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_89])).
% 17.83/9.07  tff(c_28160, plain, (![A_1687, B_1688, C_1689]: (r1_orders_2(A_1687, k1_yellow_0(A_1687, B_1688), k1_yellow_0(A_1687, C_1689)) | ~r1_yellow_0(A_1687, C_1689) | ~r1_yellow_0(A_1687, B_1688) | ~r1_tarski(B_1688, C_1689) | ~l1_orders_2(A_1687))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.83/9.07  tff(c_28163, plain, (![C_1689]: (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), k1_yellow_0('#skF_4', C_1689)) | ~r1_yellow_0('#skF_4', C_1689) | ~r1_yellow_0('#skF_4', k1_xboole_0) | ~r1_tarski(k1_xboole_0, C_1689) | ~l1_orders_2('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_28160])).
% 17.83/9.07  tff(c_28168, plain, (![C_1689]: (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), k1_yellow_0('#skF_4', C_1689)) | ~r1_yellow_0('#skF_4', C_1689) | ~r1_yellow_0('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2, c_28163])).
% 17.83/9.07  tff(c_28171, plain, (~r1_yellow_0('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_28168])).
% 17.83/9.07  tff(c_28174, plain, (~l1_orders_2('#skF_4') | ~v1_yellow_0('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_28171])).
% 17.83/9.07  tff(c_28177, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_28174])).
% 17.83/9.07  tff(c_28179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_28177])).
% 17.83/9.07  tff(c_28180, plain, (![C_1689]: (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), k1_yellow_0('#skF_4', C_1689)) | ~r1_yellow_0('#skF_4', C_1689))), inference(splitRight, [status(thm)], [c_28168])).
% 17.83/9.07  tff(c_28322, plain, (![D_1705, B_1706, A_1707, C_1708]: (r2_hidden(D_1705, B_1706) | ~r1_orders_2(A_1707, C_1708, D_1705) | ~r2_hidden(C_1708, B_1706) | ~m1_subset_1(D_1705, u1_struct_0(A_1707)) | ~m1_subset_1(C_1708, u1_struct_0(A_1707)) | ~v13_waybel_0(B_1706, A_1707) | ~m1_subset_1(B_1706, k1_zfmisc_1(u1_struct_0(A_1707))) | ~l1_orders_2(A_1707))), inference(cnfTransformation, [status(thm)], [f_103])).
% 17.83/9.07  tff(c_28334, plain, (![C_1689, B_1706]: (r2_hidden(k1_yellow_0('#skF_4', C_1689), B_1706) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1706) | ~m1_subset_1(k1_yellow_0('#skF_4', C_1689), u1_struct_0('#skF_4')) | ~m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1706, '#skF_4') | ~m1_subset_1(B_1706, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~r1_yellow_0('#skF_4', C_1689))), inference(resolution, [status(thm)], [c_28180, c_28322])).
% 17.83/9.07  tff(c_28356, plain, (![C_1689, B_1706]: (r2_hidden(k1_yellow_0('#skF_4', C_1689), B_1706) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1706) | ~m1_subset_1(k1_yellow_0('#skF_4', C_1689), u1_struct_0('#skF_4')) | ~m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1706, '#skF_4') | ~m1_subset_1(B_1706, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', C_1689))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_28334])).
% 17.83/9.07  tff(c_28645, plain, (~m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_28356])).
% 17.83/9.07  tff(c_28654, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_157, c_28645])).
% 17.83/9.07  tff(c_28661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_28654])).
% 17.83/9.07  tff(c_28777, plain, (![C_1725, B_1726]: (r2_hidden(k1_yellow_0('#skF_4', C_1725), B_1726) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1726) | ~m1_subset_1(k1_yellow_0('#skF_4', C_1725), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1726, '#skF_4') | ~m1_subset_1(B_1726, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', C_1725))), inference(splitRight, [status(thm)], [c_28356])).
% 17.83/9.07  tff(c_28782, plain, (![B_5, B_1726]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))), B_1726) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1726) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1726, '#skF_4') | ~m1_subset_1(B_1726, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_28211, c_28777])).
% 17.83/9.07  tff(c_28802, plain, (![B_5, B_1726]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))), B_1726) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1726) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1726, '#skF_4') | ~m1_subset_1(B_1726, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_28782])).
% 17.83/9.07  tff(c_32845, plain, (![B_1922, B_1923]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_1922))), B_1923) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1923) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1922), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1923, '#skF_4') | ~m1_subset_1(B_1923, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_1922))) | u1_struct_0('#skF_4')=B_1922 | ~m1_subset_1(B_1922, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_28802])).
% 17.83/9.07  tff(c_32880, plain, (![B_5, B_1923]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), B_1923) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1923) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1923, '#skF_4') | ~m1_subset_1(B_1923, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_28211, c_32845])).
% 17.83/9.07  tff(c_32903, plain, (![B_5, B_1923]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), B_1923) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1923) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1923, '#skF_4') | ~m1_subset_1(B_1923, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_32880])).
% 17.83/9.07  tff(c_32905, plain, (![B_1924, B_1925]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1924), B_1925) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1925) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1924), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1925, '#skF_4') | ~m1_subset_1(B_1925, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_1924))) | u1_struct_0('#skF_4')=B_1924 | ~m1_subset_1(B_1924, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_32903])).
% 17.83/9.07  tff(c_32908, plain, (![B_1924, B_1925]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1924), B_1925) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1925) | ~v13_waybel_0(B_1925, '#skF_4') | ~m1_subset_1(B_1925, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_1924 | ~m1_subset_1(B_1924, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1924), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_32905])).
% 17.83/9.07  tff(c_32911, plain, (![B_1924, B_1925]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1924), B_1925) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1925) | ~v13_waybel_0(B_1925, '#skF_4') | ~m1_subset_1(B_1925, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_1924 | ~m1_subset_1(B_1924, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1924), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_32908])).
% 17.83/9.07  tff(c_32913, plain, (![B_1926, B_1927]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1926), B_1927) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1927) | ~v13_waybel_0(B_1927, '#skF_4') | ~m1_subset_1(B_1927, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_1926 | ~m1_subset_1(B_1926, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1926), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_32911])).
% 17.83/9.07  tff(c_32922, plain, (![B_1928, B_1929]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1928), B_1929) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1929) | ~v13_waybel_0(B_1929, '#skF_4') | ~m1_subset_1(B_1929, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_1928 | ~m1_subset_1(B_1928, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_10, c_32913])).
% 17.83/9.07  tff(c_8, plain, (![A_4, B_5]: (~r2_hidden('#skF_1'(A_4, B_5), B_5) | B_5=A_4 | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 17.83/9.07  tff(c_32963, plain, (![B_1930]: (~r2_hidden(k3_yellow_0('#skF_4'), B_1930) | ~v13_waybel_0(B_1930, '#skF_4') | u1_struct_0('#skF_4')=B_1930 | ~m1_subset_1(B_1930, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_32922, c_8])).
% 17.83/9.07  tff(c_32970, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v13_waybel_0('#skF_5', '#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_46, c_32963])).
% 17.83/9.07  tff(c_32978, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_134, c_32970])).
% 17.83/9.07  tff(c_12, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 17.83/9.07  tff(c_290, plain, (![A_103, B_104]: (k1_yellow_0(A_103, k5_waybel_0(A_103, B_104))=B_104 | ~m1_subset_1(B_104, u1_struct_0(A_103)) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.83/9.07  tff(c_307, plain, (![A_103, B_5]: (k1_yellow_0(A_103, k5_waybel_0(A_103, '#skF_1'(u1_struct_0(A_103), B_5)))='#skF_1'(u1_struct_0(A_103), B_5) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103) | u1_struct_0(A_103)=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_103))))), inference(resolution, [status(thm)], [c_10, c_290])).
% 17.83/9.07  tff(c_268, plain, (![A_100, B_101, C_102]: (r1_orders_2(A_100, k1_yellow_0(A_100, B_101), k1_yellow_0(A_100, C_102)) | ~r1_yellow_0(A_100, C_102) | ~r1_yellow_0(A_100, B_101) | ~r1_tarski(B_101, C_102) | ~l1_orders_2(A_100))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.83/9.07  tff(c_271, plain, (![C_102]: (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), k1_yellow_0('#skF_4', C_102)) | ~r1_yellow_0('#skF_4', C_102) | ~r1_yellow_0('#skF_4', k1_xboole_0) | ~r1_tarski(k1_xboole_0, C_102) | ~l1_orders_2('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_268])).
% 17.83/9.07  tff(c_276, plain, (![C_102]: (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), k1_yellow_0('#skF_4', C_102)) | ~r1_yellow_0('#skF_4', C_102) | ~r1_yellow_0('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2, c_271])).
% 17.83/9.07  tff(c_279, plain, (~r1_yellow_0('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_276])).
% 17.83/9.07  tff(c_282, plain, (~l1_orders_2('#skF_4') | ~v1_yellow_0('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_279])).
% 17.83/9.07  tff(c_285, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_282])).
% 17.83/9.07  tff(c_287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_285])).
% 17.83/9.07  tff(c_289, plain, (r1_yellow_0('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_276])).
% 17.83/9.07  tff(c_288, plain, (![C_102]: (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), k1_yellow_0('#skF_4', C_102)) | ~r1_yellow_0('#skF_4', C_102))), inference(splitRight, [status(thm)], [c_276])).
% 17.83/9.07  tff(c_400, plain, (![D_113, B_114, A_115, C_116]: (r2_hidden(D_113, B_114) | ~r1_orders_2(A_115, C_116, D_113) | ~r2_hidden(C_116, B_114) | ~m1_subset_1(D_113, u1_struct_0(A_115)) | ~m1_subset_1(C_116, u1_struct_0(A_115)) | ~v13_waybel_0(B_114, A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_orders_2(A_115))), inference(cnfTransformation, [status(thm)], [f_103])).
% 17.83/9.07  tff(c_410, plain, (![C_102, B_114]: (r2_hidden(k1_yellow_0('#skF_4', C_102), B_114) | ~r2_hidden(k3_yellow_0('#skF_4'), B_114) | ~m1_subset_1(k1_yellow_0('#skF_4', C_102), u1_struct_0('#skF_4')) | ~m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_114, '#skF_4') | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~r1_yellow_0('#skF_4', C_102))), inference(resolution, [status(thm)], [c_288, c_400])).
% 17.83/9.07  tff(c_429, plain, (![C_102, B_114]: (r2_hidden(k1_yellow_0('#skF_4', C_102), B_114) | ~r2_hidden(k3_yellow_0('#skF_4'), B_114) | ~m1_subset_1(k1_yellow_0('#skF_4', C_102), u1_struct_0('#skF_4')) | ~m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_114, '#skF_4') | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', C_102))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_410])).
% 17.83/9.07  tff(c_750, plain, (~m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_429])).
% 17.83/9.07  tff(c_753, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_157, c_750])).
% 17.83/9.07  tff(c_760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_753])).
% 17.83/9.07  tff(c_885, plain, (![C_139, B_140]: (r2_hidden(k1_yellow_0('#skF_4', C_139), B_140) | ~r2_hidden(k3_yellow_0('#skF_4'), B_140) | ~m1_subset_1(k1_yellow_0('#skF_4', C_139), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_140, '#skF_4') | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', C_139))), inference(splitRight, [status(thm)], [c_429])).
% 17.83/9.07  tff(c_890, plain, (![B_5, B_140]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))), B_140) | ~r2_hidden(k3_yellow_0('#skF_4'), B_140) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_140, '#skF_4') | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_307, c_885])).
% 17.83/9.07  tff(c_910, plain, (![B_5, B_140]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))), B_140) | ~r2_hidden(k3_yellow_0('#skF_4'), B_140) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_140, '#skF_4') | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_890])).
% 17.83/9.07  tff(c_6049, plain, (![B_448, B_449]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_448))), B_449) | ~r2_hidden(k3_yellow_0('#skF_4'), B_449) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_448), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_449, '#skF_4') | ~m1_subset_1(B_449, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_448))) | u1_struct_0('#skF_4')=B_448 | ~m1_subset_1(B_448, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_910])).
% 17.83/9.07  tff(c_6084, plain, (![B_5, B_449]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), B_449) | ~r2_hidden(k3_yellow_0('#skF_4'), B_449) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_449, '#skF_4') | ~m1_subset_1(B_449, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_307, c_6049])).
% 17.83/9.07  tff(c_6107, plain, (![B_5, B_449]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), B_449) | ~r2_hidden(k3_yellow_0('#skF_4'), B_449) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_449, '#skF_4') | ~m1_subset_1(B_449, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_6084])).
% 17.83/9.07  tff(c_6109, plain, (![B_450, B_451]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_450), B_451) | ~r2_hidden(k3_yellow_0('#skF_4'), B_451) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_450), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_451, '#skF_4') | ~m1_subset_1(B_451, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_450))) | u1_struct_0('#skF_4')=B_450 | ~m1_subset_1(B_450, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_6107])).
% 17.83/9.07  tff(c_6112, plain, (![B_450, B_451]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_450), B_451) | ~r2_hidden(k3_yellow_0('#skF_4'), B_451) | ~v13_waybel_0(B_451, '#skF_4') | ~m1_subset_1(B_451, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_450 | ~m1_subset_1(B_450, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_450), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_6109])).
% 17.83/9.07  tff(c_6115, plain, (![B_450, B_451]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_450), B_451) | ~r2_hidden(k3_yellow_0('#skF_4'), B_451) | ~v13_waybel_0(B_451, '#skF_4') | ~m1_subset_1(B_451, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_450 | ~m1_subset_1(B_450, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_450), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_6112])).
% 17.83/9.07  tff(c_6117, plain, (![B_452, B_453]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_452), B_453) | ~r2_hidden(k3_yellow_0('#skF_4'), B_453) | ~v13_waybel_0(B_453, '#skF_4') | ~m1_subset_1(B_453, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_452 | ~m1_subset_1(B_452, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_452), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_6115])).
% 17.83/9.07  tff(c_6126, plain, (![B_454, B_455]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_454), B_455) | ~r2_hidden(k3_yellow_0('#skF_4'), B_455) | ~v13_waybel_0(B_455, '#skF_4') | ~m1_subset_1(B_455, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_454 | ~m1_subset_1(B_454, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_10, c_6117])).
% 17.83/9.07  tff(c_6167, plain, (![B_456]: (~r2_hidden(k3_yellow_0('#skF_4'), B_456) | ~v13_waybel_0(B_456, '#skF_4') | u1_struct_0('#skF_4')=B_456 | ~m1_subset_1(B_456, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_6126, c_8])).
% 17.83/9.07  tff(c_6174, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v13_waybel_0('#skF_5', '#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_46, c_6167])).
% 17.83/9.07  tff(c_6182, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_134, c_6174])).
% 17.83/9.07  tff(c_301, plain, (![A_65]: (k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', A_65))=A_65 | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r2_hidden(A_65, '#skF_5'))), inference(resolution, [status(thm)], [c_157, c_290])).
% 17.83/9.07  tff(c_310, plain, (![A_65]: (k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', A_65))=A_65 | v2_struct_0('#skF_4') | ~r2_hidden(A_65, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_301])).
% 17.83/9.07  tff(c_311, plain, (![A_65]: (k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', A_65))=A_65 | ~r2_hidden(A_65, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_310])).
% 17.83/9.07  tff(c_2164, plain, (![B_255, B_256]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_255))), B_256) | ~r2_hidden(k3_yellow_0('#skF_4'), B_256) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_255), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_256, '#skF_4') | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_255))) | u1_struct_0('#skF_4')=B_255 | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_910])).
% 17.83/9.07  tff(c_2191, plain, (![B_5, B_256]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), B_256) | ~r2_hidden(k3_yellow_0('#skF_4'), B_256) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_256, '#skF_4') | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_307, c_2164])).
% 17.83/9.07  tff(c_2208, plain, (![B_5, B_256]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), B_256) | ~r2_hidden(k3_yellow_0('#skF_4'), B_256) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_256, '#skF_4') | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_2191])).
% 17.83/9.07  tff(c_2211, plain, (![B_258, B_259]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_258), B_259) | ~r2_hidden(k3_yellow_0('#skF_4'), B_259) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_258), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_259, '#skF_4') | ~m1_subset_1(B_259, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_258))) | u1_struct_0('#skF_4')=B_258 | ~m1_subset_1(B_258, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_2208])).
% 17.83/9.07  tff(c_2214, plain, (![B_258, B_259]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_258), B_259) | ~r2_hidden(k3_yellow_0('#skF_4'), B_259) | ~v13_waybel_0(B_259, '#skF_4') | ~m1_subset_1(B_259, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_258 | ~m1_subset_1(B_258, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_258), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_2211])).
% 17.83/9.07  tff(c_2217, plain, (![B_258, B_259]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_258), B_259) | ~r2_hidden(k3_yellow_0('#skF_4'), B_259) | ~v13_waybel_0(B_259, '#skF_4') | ~m1_subset_1(B_259, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_258 | ~m1_subset_1(B_258, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_258), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_2214])).
% 17.83/9.07  tff(c_2219, plain, (![B_260, B_261]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_260), B_261) | ~r2_hidden(k3_yellow_0('#skF_4'), B_261) | ~v13_waybel_0(B_261, '#skF_4') | ~m1_subset_1(B_261, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_260 | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_260), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_2217])).
% 17.83/9.07  tff(c_2228, plain, (![B_262, B_263]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_262), B_263) | ~r2_hidden(k3_yellow_0('#skF_4'), B_263) | ~v13_waybel_0(B_263, '#skF_4') | ~m1_subset_1(B_263, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_262 | ~m1_subset_1(B_262, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_10, c_2219])).
% 17.83/9.07  tff(c_2255, plain, (![B_264]: (~r2_hidden(k3_yellow_0('#skF_4'), B_264) | ~v13_waybel_0(B_264, '#skF_4') | u1_struct_0('#skF_4')=B_264 | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2228, c_8])).
% 17.83/9.07  tff(c_2262, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v13_waybel_0('#skF_5', '#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_46, c_2255])).
% 17.83/9.07  tff(c_2270, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_134, c_2262])).
% 17.83/9.07  tff(c_36, plain, (![A_20, B_34]: (m1_subset_1('#skF_2'(A_20, B_34), u1_struct_0(A_20)) | v13_waybel_0(B_34, A_20) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_103])).
% 17.83/9.07  tff(c_207, plain, (![A_81, B_82]: (r2_hidden('#skF_2'(A_81, B_82), B_82) | v13_waybel_0(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_orders_2(A_81))), inference(cnfTransformation, [status(thm)], [f_103])).
% 17.83/9.07  tff(c_221, plain, (![A_83]: (r2_hidden('#skF_2'(A_83, u1_struct_0(A_83)), u1_struct_0(A_83)) | v13_waybel_0(u1_struct_0(A_83), A_83) | ~l1_orders_2(A_83))), inference(resolution, [status(thm)], [c_73, c_207])).
% 17.83/9.07  tff(c_158, plain, (![A_65, A_3]: (m1_subset_1(A_65, A_3) | ~r2_hidden(A_65, A_3))), inference(resolution, [status(thm)], [c_73, c_152])).
% 17.83/9.07  tff(c_225, plain, (![A_83]: (m1_subset_1('#skF_2'(A_83, u1_struct_0(A_83)), u1_struct_0(A_83)) | v13_waybel_0(u1_struct_0(A_83), A_83) | ~l1_orders_2(A_83))), inference(resolution, [status(thm)], [c_221, c_158])).
% 17.83/9.07  tff(c_505, plain, (![A_125]: (k1_yellow_0(A_125, k5_waybel_0(A_125, '#skF_2'(A_125, u1_struct_0(A_125))))='#skF_2'(A_125, u1_struct_0(A_125)) | ~v5_orders_2(A_125) | ~v4_orders_2(A_125) | ~v3_orders_2(A_125) | v2_struct_0(A_125) | v13_waybel_0(u1_struct_0(A_125), A_125) | ~l1_orders_2(A_125))), inference(resolution, [status(thm)], [c_225, c_290])).
% 17.83/9.07  tff(c_524, plain, (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), '#skF_2'('#skF_4', u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_2'('#skF_4', u1_struct_0('#skF_4')))) | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | v13_waybel_0(u1_struct_0('#skF_4'), '#skF_4') | ~l1_orders_2('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_505, c_288])).
% 17.83/9.07  tff(c_553, plain, (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), '#skF_2'('#skF_4', u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_2'('#skF_4', u1_struct_0('#skF_4')))) | v2_struct_0('#skF_4') | v13_waybel_0(u1_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_62, c_60, c_58, c_524])).
% 17.83/9.07  tff(c_554, plain, (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), '#skF_2'('#skF_4', u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_2'('#skF_4', u1_struct_0('#skF_4')))) | v13_waybel_0(u1_struct_0('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_553])).
% 17.83/9.07  tff(c_579, plain, (~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_2'('#skF_4', u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_554])).
% 17.83/9.07  tff(c_582, plain, (~m1_subset_1('#skF_2'('#skF_4', u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_579])).
% 17.83/9.07  tff(c_585, plain, (~m1_subset_1('#skF_2'('#skF_4', u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_582])).
% 17.83/9.07  tff(c_586, plain, (~m1_subset_1('#skF_2'('#skF_4', u1_struct_0('#skF_4')), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_585])).
% 17.83/9.07  tff(c_589, plain, (v13_waybel_0(u1_struct_0('#skF_4'), '#skF_4') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_36, c_586])).
% 17.83/9.07  tff(c_598, plain, (v13_waybel_0(u1_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_73, c_589])).
% 17.83/9.07  tff(c_924, plain, (![C_141, B_142]: (r2_hidden(k1_yellow_0('#skF_4', C_141), B_142) | ~r2_hidden(k3_yellow_0('#skF_4'), B_142) | ~v13_waybel_0(B_142, '#skF_4') | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', C_141) | ~r2_hidden(k1_yellow_0('#skF_4', C_141), '#skF_5'))), inference(resolution, [status(thm)], [c_157, c_885])).
% 17.83/9.07  tff(c_932, plain, (![C_141]: (r2_hidden(k1_yellow_0('#skF_4', C_141), u1_struct_0('#skF_4')) | ~r2_hidden(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~v13_waybel_0(u1_struct_0('#skF_4'), '#skF_4') | ~r1_yellow_0('#skF_4', C_141) | ~r2_hidden(k1_yellow_0('#skF_4', C_141), '#skF_5'))), inference(resolution, [status(thm)], [c_73, c_924])).
% 17.83/9.07  tff(c_939, plain, (![C_141]: (r2_hidden(k1_yellow_0('#skF_4', C_141), u1_struct_0('#skF_4')) | ~r2_hidden(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~r1_yellow_0('#skF_4', C_141) | ~r2_hidden(k1_yellow_0('#skF_4', C_141), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_598, c_932])).
% 17.83/9.07  tff(c_940, plain, (~r2_hidden(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_939])).
% 17.83/9.07  tff(c_2446, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2270, c_940])).
% 17.83/9.07  tff(c_2463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_2446])).
% 17.83/9.07  tff(c_2471, plain, (![C_267]: (r2_hidden(k1_yellow_0('#skF_4', C_267), u1_struct_0('#skF_4')) | ~r1_yellow_0('#skF_4', C_267) | ~r2_hidden(k1_yellow_0('#skF_4', C_267), '#skF_5'))), inference(splitRight, [status(thm)], [c_939])).
% 17.83/9.07  tff(c_2523, plain, (![A_269]: (r2_hidden(A_269, u1_struct_0('#skF_4')) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', A_269)) | ~r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', A_269)), '#skF_5') | ~r2_hidden(A_269, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_2471])).
% 17.83/9.07  tff(c_2566, plain, (![A_270]: (r2_hidden(A_270, u1_struct_0('#skF_4')) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', A_270)) | ~r2_hidden(A_270, '#skF_5') | ~r2_hidden(A_270, '#skF_5') | ~r2_hidden(A_270, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_2523])).
% 17.83/9.07  tff(c_2631, plain, (![A_273]: (u1_struct_0('#skF_4')=A_273 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_273)) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(A_273, u1_struct_0('#skF_4')))) | ~r2_hidden('#skF_1'(A_273, u1_struct_0('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_2566, c_8])).
% 17.83/9.07  tff(c_2634, plain, (![A_273]: (u1_struct_0('#skF_4')=A_273 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_273)) | ~r2_hidden('#skF_1'(A_273, u1_struct_0('#skF_4')), '#skF_5') | ~m1_subset_1('#skF_1'(A_273, u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_2631])).
% 17.83/9.07  tff(c_2637, plain, (![A_273]: (u1_struct_0('#skF_4')=A_273 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_273)) | ~r2_hidden('#skF_1'(A_273, u1_struct_0('#skF_4')), '#skF_5') | ~m1_subset_1('#skF_1'(A_273, u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_2634])).
% 17.83/9.07  tff(c_2649, plain, (![A_277]: (u1_struct_0('#skF_4')=A_277 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_277)) | ~r2_hidden('#skF_1'(A_277, u1_struct_0('#skF_4')), '#skF_5') | ~m1_subset_1('#skF_1'(A_277, u1_struct_0('#skF_4')), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_2637])).
% 17.83/9.07  tff(c_2662, plain, (![A_278]: (u1_struct_0('#skF_4')=A_278 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_278)) | ~r2_hidden('#skF_1'(A_278, u1_struct_0('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_157, c_2649])).
% 17.83/9.07  tff(c_2665, plain, (![A_278]: (u1_struct_0('#skF_4')=A_278 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_278)) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_1'(A_278, u1_struct_0('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_12, c_2662])).
% 17.83/9.07  tff(c_2669, plain, (![A_279]: (u1_struct_0('#skF_4')=A_279 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_279)) | ~m1_subset_1('#skF_1'(A_279, u1_struct_0('#skF_4')), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_52, c_2665])).
% 17.83/9.07  tff(c_2674, plain, (u1_struct_0('#skF_4')='#skF_5' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_2669])).
% 17.83/9.07  tff(c_2688, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_2674])).
% 17.83/9.07  tff(c_6258, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6182, c_2688])).
% 17.83/9.07  tff(c_6284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_6258])).
% 17.83/9.07  tff(c_6285, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_2674])).
% 17.83/9.07  tff(c_169, plain, (![A_71, B_72]: (~r2_hidden('#skF_1'(A_71, B_72), B_72) | B_72=A_71 | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 17.83/9.07  tff(c_187, plain, (![B_77, A_78]: (B_77=A_78 | ~m1_subset_1(B_77, k1_zfmisc_1(A_78)) | v1_xboole_0(B_77) | ~m1_subset_1('#skF_1'(A_78, B_77), B_77))), inference(resolution, [status(thm)], [c_12, c_169])).
% 17.83/9.07  tff(c_200, plain, (![A_78]: (u1_struct_0('#skF_4')=A_78 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_78)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(A_78, u1_struct_0('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_157, c_187])).
% 17.83/9.07  tff(c_206, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_200])).
% 17.83/9.07  tff(c_6344, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6285, c_206])).
% 17.83/9.07  tff(c_6352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_6344])).
% 17.83/9.07  tff(c_6353, plain, (v13_waybel_0(u1_struct_0('#skF_4'), '#skF_4') | r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), '#skF_2'('#skF_4', u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_554])).
% 17.83/9.07  tff(c_6355, plain, (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), '#skF_2'('#skF_4', u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_6353])).
% 17.83/9.07  tff(c_26, plain, (![D_43, B_34, A_20, C_41]: (r2_hidden(D_43, B_34) | ~r1_orders_2(A_20, C_41, D_43) | ~r2_hidden(C_41, B_34) | ~m1_subset_1(D_43, u1_struct_0(A_20)) | ~m1_subset_1(C_41, u1_struct_0(A_20)) | ~v13_waybel_0(B_34, A_20) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_103])).
% 17.83/9.07  tff(c_6360, plain, (![B_34]: (r2_hidden('#skF_2'('#skF_4', u1_struct_0('#skF_4')), B_34) | ~r2_hidden(k3_yellow_0('#skF_4'), B_34) | ~m1_subset_1('#skF_2'('#skF_4', u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_34, '#skF_4') | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_6355, c_26])).
% 17.83/9.07  tff(c_6363, plain, (![B_34]: (r2_hidden('#skF_2'('#skF_4', u1_struct_0('#skF_4')), B_34) | ~r2_hidden(k3_yellow_0('#skF_4'), B_34) | ~m1_subset_1('#skF_2'('#skF_4', u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_34, '#skF_4') | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6360])).
% 17.83/9.07  tff(c_6542, plain, (~m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_6363])).
% 17.83/9.07  tff(c_6551, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_157, c_6542])).
% 17.83/9.07  tff(c_6558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_6551])).
% 17.83/9.07  tff(c_6560, plain, (m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_6363])).
% 17.83/9.07  tff(c_6715, plain, (![C_479, B_480]: (r2_hidden(k1_yellow_0('#skF_4', C_479), B_480) | ~r2_hidden(k3_yellow_0('#skF_4'), B_480) | ~m1_subset_1(k1_yellow_0('#skF_4', C_479), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_480, '#skF_4') | ~m1_subset_1(B_480, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', C_479))), inference(demodulation, [status(thm), theory('equality')], [c_6560, c_429])).
% 17.83/9.07  tff(c_6723, plain, (![B_5, B_480]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))), B_480) | ~r2_hidden(k3_yellow_0('#skF_4'), B_480) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_480, '#skF_4') | ~m1_subset_1(B_480, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_307, c_6715])).
% 17.83/9.07  tff(c_6743, plain, (![B_5, B_480]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))), B_480) | ~r2_hidden(k3_yellow_0('#skF_4'), B_480) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_480, '#skF_4') | ~m1_subset_1(B_480, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_6723])).
% 17.83/9.07  tff(c_11416, plain, (![B_751, B_752]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_751))), B_752) | ~r2_hidden(k3_yellow_0('#skF_4'), B_752) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_751), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_752, '#skF_4') | ~m1_subset_1(B_752, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_751))) | u1_struct_0('#skF_4')=B_751 | ~m1_subset_1(B_751, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_6743])).
% 17.83/9.07  tff(c_11451, plain, (![B_5, B_752]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), B_752) | ~r2_hidden(k3_yellow_0('#skF_4'), B_752) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_752, '#skF_4') | ~m1_subset_1(B_752, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_307, c_11416])).
% 17.83/9.07  tff(c_11474, plain, (![B_5, B_752]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), B_752) | ~r2_hidden(k3_yellow_0('#skF_4'), B_752) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_752, '#skF_4') | ~m1_subset_1(B_752, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_11451])).
% 17.83/9.07  tff(c_11476, plain, (![B_753, B_754]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_753), B_754) | ~r2_hidden(k3_yellow_0('#skF_4'), B_754) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_753), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_754, '#skF_4') | ~m1_subset_1(B_754, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_753))) | u1_struct_0('#skF_4')=B_753 | ~m1_subset_1(B_753, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_11474])).
% 17.83/9.07  tff(c_11479, plain, (![B_753, B_754]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_753), B_754) | ~r2_hidden(k3_yellow_0('#skF_4'), B_754) | ~v13_waybel_0(B_754, '#skF_4') | ~m1_subset_1(B_754, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_753 | ~m1_subset_1(B_753, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_753), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_11476])).
% 17.83/9.07  tff(c_11482, plain, (![B_753, B_754]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_753), B_754) | ~r2_hidden(k3_yellow_0('#skF_4'), B_754) | ~v13_waybel_0(B_754, '#skF_4') | ~m1_subset_1(B_754, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_753 | ~m1_subset_1(B_753, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_753), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_11479])).
% 17.83/9.07  tff(c_11484, plain, (![B_755, B_756]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_755), B_756) | ~r2_hidden(k3_yellow_0('#skF_4'), B_756) | ~v13_waybel_0(B_756, '#skF_4') | ~m1_subset_1(B_756, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_755 | ~m1_subset_1(B_755, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_755), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_11482])).
% 17.83/9.07  tff(c_11493, plain, (![B_757, B_758]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_757), B_758) | ~r2_hidden(k3_yellow_0('#skF_4'), B_758) | ~v13_waybel_0(B_758, '#skF_4') | ~m1_subset_1(B_758, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_757 | ~m1_subset_1(B_757, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_10, c_11484])).
% 17.83/9.07  tff(c_11528, plain, (![B_759]: (~r2_hidden(k3_yellow_0('#skF_4'), B_759) | ~v13_waybel_0(B_759, '#skF_4') | u1_struct_0('#skF_4')=B_759 | ~m1_subset_1(B_759, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_11493, c_8])).
% 17.83/9.07  tff(c_11535, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v13_waybel_0('#skF_5', '#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_46, c_11528])).
% 17.83/9.07  tff(c_11543, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_134, c_11535])).
% 17.83/9.07  tff(c_7864, plain, (![B_579, B_580]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_579))), B_580) | ~r2_hidden(k3_yellow_0('#skF_4'), B_580) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_579), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_580, '#skF_4') | ~m1_subset_1(B_580, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_579))) | u1_struct_0('#skF_4')=B_579 | ~m1_subset_1(B_579, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_6743])).
% 17.83/9.07  tff(c_7887, plain, (![B_5, B_580]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), B_580) | ~r2_hidden(k3_yellow_0('#skF_4'), B_580) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_580, '#skF_4') | ~m1_subset_1(B_580, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_307, c_7864])).
% 17.83/9.07  tff(c_7902, plain, (![B_5, B_580]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), B_580) | ~r2_hidden(k3_yellow_0('#skF_4'), B_580) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_580, '#skF_4') | ~m1_subset_1(B_580, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_7887])).
% 17.83/9.07  tff(c_7904, plain, (![B_581, B_582]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_581), B_582) | ~r2_hidden(k3_yellow_0('#skF_4'), B_582) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_581), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_582, '#skF_4') | ~m1_subset_1(B_582, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_581))) | u1_struct_0('#skF_4')=B_581 | ~m1_subset_1(B_581, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_7902])).
% 17.83/9.07  tff(c_7907, plain, (![B_581, B_582]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_581), B_582) | ~r2_hidden(k3_yellow_0('#skF_4'), B_582) | ~v13_waybel_0(B_582, '#skF_4') | ~m1_subset_1(B_582, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_581 | ~m1_subset_1(B_581, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_581), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_7904])).
% 17.83/9.07  tff(c_7910, plain, (![B_581, B_582]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_581), B_582) | ~r2_hidden(k3_yellow_0('#skF_4'), B_582) | ~v13_waybel_0(B_582, '#skF_4') | ~m1_subset_1(B_582, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_581 | ~m1_subset_1(B_581, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_581), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_7907])).
% 17.83/9.07  tff(c_7912, plain, (![B_583, B_584]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_583), B_584) | ~r2_hidden(k3_yellow_0('#skF_4'), B_584) | ~v13_waybel_0(B_584, '#skF_4') | ~m1_subset_1(B_584, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_583 | ~m1_subset_1(B_583, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_583), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_7910])).
% 17.83/9.07  tff(c_7921, plain, (![B_585, B_586]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_585), B_586) | ~r2_hidden(k3_yellow_0('#skF_4'), B_586) | ~v13_waybel_0(B_586, '#skF_4') | ~m1_subset_1(B_586, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_585 | ~m1_subset_1(B_585, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_10, c_7912])).
% 17.83/9.07  tff(c_7945, plain, (![B_587]: (~r2_hidden(k3_yellow_0('#skF_4'), B_587) | ~v13_waybel_0(B_587, '#skF_4') | u1_struct_0('#skF_4')=B_587 | ~m1_subset_1(B_587, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_7921, c_8])).
% 17.83/9.07  tff(c_7952, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v13_waybel_0('#skF_5', '#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_46, c_7945])).
% 17.83/9.07  tff(c_7960, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_134, c_7952])).
% 17.83/9.07  tff(c_34, plain, (![A_20, B_34]: (m1_subset_1('#skF_3'(A_20, B_34), u1_struct_0(A_20)) | v13_waybel_0(B_34, A_20) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_103])).
% 17.83/9.07  tff(c_6365, plain, (![A_463, B_464]: (k1_yellow_0(A_463, k5_waybel_0(A_463, '#skF_3'(A_463, B_464)))='#skF_3'(A_463, B_464) | ~v5_orders_2(A_463) | ~v4_orders_2(A_463) | ~v3_orders_2(A_463) | v2_struct_0(A_463) | v13_waybel_0(B_464, A_463) | ~m1_subset_1(B_464, k1_zfmisc_1(u1_struct_0(A_463))) | ~l1_orders_2(A_463))), inference(resolution, [status(thm)], [c_34, c_290])).
% 17.83/9.07  tff(c_6445, plain, (![A_468]: (k1_yellow_0(A_468, k5_waybel_0(A_468, '#skF_3'(A_468, u1_struct_0(A_468))))='#skF_3'(A_468, u1_struct_0(A_468)) | ~v5_orders_2(A_468) | ~v4_orders_2(A_468) | ~v3_orders_2(A_468) | v2_struct_0(A_468) | v13_waybel_0(u1_struct_0(A_468), A_468) | ~l1_orders_2(A_468))), inference(resolution, [status(thm)], [c_73, c_6365])).
% 17.83/9.07  tff(c_6464, plain, (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), '#skF_3'('#skF_4', u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_3'('#skF_4', u1_struct_0('#skF_4')))) | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | v13_waybel_0(u1_struct_0('#skF_4'), '#skF_4') | ~l1_orders_2('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6445, c_288])).
% 17.83/9.07  tff(c_6493, plain, (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), '#skF_3'('#skF_4', u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_3'('#skF_4', u1_struct_0('#skF_4')))) | v2_struct_0('#skF_4') | v13_waybel_0(u1_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_62, c_60, c_58, c_6464])).
% 17.83/9.07  tff(c_6494, plain, (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), '#skF_3'('#skF_4', u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_3'('#skF_4', u1_struct_0('#skF_4')))) | v13_waybel_0(u1_struct_0('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_6493])).
% 17.83/9.07  tff(c_6504, plain, (~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_3'('#skF_4', u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_6494])).
% 17.83/9.07  tff(c_6508, plain, (~m1_subset_1('#skF_3'('#skF_4', u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_6504])).
% 17.83/9.07  tff(c_6511, plain, (~m1_subset_1('#skF_3'('#skF_4', u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_6508])).
% 17.83/9.07  tff(c_6512, plain, (~m1_subset_1('#skF_3'('#skF_4', u1_struct_0('#skF_4')), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_6511])).
% 17.83/9.07  tff(c_6515, plain, (v13_waybel_0(u1_struct_0('#skF_4'), '#skF_4') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_34, c_6512])).
% 17.83/9.07  tff(c_6521, plain, (v13_waybel_0(u1_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_73, c_6515])).
% 17.83/9.07  tff(c_6754, plain, (![C_481, B_482]: (r2_hidden(k1_yellow_0('#skF_4', C_481), B_482) | ~r2_hidden(k3_yellow_0('#skF_4'), B_482) | ~v13_waybel_0(B_482, '#skF_4') | ~m1_subset_1(B_482, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', C_481) | ~r2_hidden(k1_yellow_0('#skF_4', C_481), '#skF_5'))), inference(resolution, [status(thm)], [c_157, c_6715])).
% 17.83/9.07  tff(c_6762, plain, (![C_481]: (r2_hidden(k1_yellow_0('#skF_4', C_481), u1_struct_0('#skF_4')) | ~r2_hidden(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~v13_waybel_0(u1_struct_0('#skF_4'), '#skF_4') | ~r1_yellow_0('#skF_4', C_481) | ~r2_hidden(k1_yellow_0('#skF_4', C_481), '#skF_5'))), inference(resolution, [status(thm)], [c_73, c_6754])).
% 17.83/9.07  tff(c_6769, plain, (![C_481]: (r2_hidden(k1_yellow_0('#skF_4', C_481), u1_struct_0('#skF_4')) | ~r2_hidden(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~r1_yellow_0('#skF_4', C_481) | ~r2_hidden(k1_yellow_0('#skF_4', C_481), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6521, c_6762])).
% 17.83/9.07  tff(c_6770, plain, (~r2_hidden(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_6769])).
% 17.83/9.07  tff(c_8000, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7960, c_6770])).
% 17.83/9.07  tff(c_8024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_8000])).
% 17.83/9.07  tff(c_8057, plain, (![C_592]: (r2_hidden(k1_yellow_0('#skF_4', C_592), u1_struct_0('#skF_4')) | ~r1_yellow_0('#skF_4', C_592) | ~r2_hidden(k1_yellow_0('#skF_4', C_592), '#skF_5'))), inference(splitRight, [status(thm)], [c_6769])).
% 17.83/9.07  tff(c_8108, plain, (![A_593]: (r2_hidden(A_593, u1_struct_0('#skF_4')) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', A_593)) | ~r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', A_593)), '#skF_5') | ~r2_hidden(A_593, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_8057])).
% 17.83/9.07  tff(c_8188, plain, (![A_595]: (r2_hidden(A_595, u1_struct_0('#skF_4')) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', A_595)) | ~r2_hidden(A_595, '#skF_5') | ~r2_hidden(A_595, '#skF_5') | ~r2_hidden(A_595, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_8108])).
% 17.83/9.07  tff(c_8224, plain, (![A_597]: (u1_struct_0('#skF_4')=A_597 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_597)) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(A_597, u1_struct_0('#skF_4')))) | ~r2_hidden('#skF_1'(A_597, u1_struct_0('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_8188, c_8])).
% 17.83/9.07  tff(c_8227, plain, (![A_597]: (u1_struct_0('#skF_4')=A_597 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_597)) | ~r2_hidden('#skF_1'(A_597, u1_struct_0('#skF_4')), '#skF_5') | ~m1_subset_1('#skF_1'(A_597, u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_8224])).
% 17.83/9.07  tff(c_8230, plain, (![A_597]: (u1_struct_0('#skF_4')=A_597 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_597)) | ~r2_hidden('#skF_1'(A_597, u1_struct_0('#skF_4')), '#skF_5') | ~m1_subset_1('#skF_1'(A_597, u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_8227])).
% 17.83/9.07  tff(c_8232, plain, (![A_598]: (u1_struct_0('#skF_4')=A_598 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_598)) | ~r2_hidden('#skF_1'(A_598, u1_struct_0('#skF_4')), '#skF_5') | ~m1_subset_1('#skF_1'(A_598, u1_struct_0('#skF_4')), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_8230])).
% 17.83/9.07  tff(c_8245, plain, (![A_599]: (u1_struct_0('#skF_4')=A_599 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_599)) | ~r2_hidden('#skF_1'(A_599, u1_struct_0('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_157, c_8232])).
% 17.83/9.07  tff(c_8248, plain, (![A_599]: (u1_struct_0('#skF_4')=A_599 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_599)) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_1'(A_599, u1_struct_0('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_12, c_8245])).
% 17.83/9.07  tff(c_8253, plain, (![A_602]: (u1_struct_0('#skF_4')=A_602 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_602)) | ~m1_subset_1('#skF_1'(A_602, u1_struct_0('#skF_4')), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_52, c_8248])).
% 17.83/9.07  tff(c_8258, plain, (u1_struct_0('#skF_4')='#skF_5' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_8253])).
% 17.83/9.07  tff(c_8259, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_8258])).
% 17.83/9.07  tff(c_11617, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_11543, c_8259])).
% 17.83/9.07  tff(c_11649, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_11617])).
% 17.83/9.07  tff(c_11650, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_8258])).
% 17.83/9.07  tff(c_11695, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11650, c_206])).
% 17.83/9.07  tff(c_11703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_11695])).
% 17.83/9.07  tff(c_11704, plain, (v13_waybel_0(u1_struct_0('#skF_4'), '#skF_4') | r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), '#skF_3'('#skF_4', u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_6494])).
% 17.83/9.07  tff(c_11706, plain, (r1_orders_2('#skF_4', k3_yellow_0('#skF_4'), '#skF_3'('#skF_4', u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_11704])).
% 17.83/9.07  tff(c_11711, plain, (![B_34]: (r2_hidden('#skF_3'('#skF_4', u1_struct_0('#skF_4')), B_34) | ~r2_hidden(k3_yellow_0('#skF_4'), B_34) | ~m1_subset_1('#skF_3'('#skF_4', u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_34, '#skF_4') | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_11706, c_26])).
% 17.83/9.07  tff(c_11714, plain, (![B_34]: (r2_hidden('#skF_3'('#skF_4', u1_struct_0('#skF_4')), B_34) | ~r2_hidden(k3_yellow_0('#skF_4'), B_34) | ~m1_subset_1('#skF_3'('#skF_4', u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_34, '#skF_4') | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_11711])).
% 17.83/9.07  tff(c_11715, plain, (~m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_11714])).
% 17.83/9.07  tff(c_11718, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_157, c_11715])).
% 17.83/9.07  tff(c_11725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_11718])).
% 17.83/9.07  tff(c_11727, plain, (m1_subset_1(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_11714])).
% 17.83/9.07  tff(c_20, plain, (![A_14, B_17, C_18]: (r1_orders_2(A_14, k1_yellow_0(A_14, B_17), k1_yellow_0(A_14, C_18)) | ~r1_yellow_0(A_14, C_18) | ~r1_yellow_0(A_14, B_17) | ~r1_tarski(B_17, C_18) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.83/9.07  tff(c_17946, plain, (![A_1099, C_1100, B_1101, B_1102]: (r2_hidden(k1_yellow_0(A_1099, C_1100), B_1101) | ~r2_hidden(k1_yellow_0(A_1099, B_1102), B_1101) | ~m1_subset_1(k1_yellow_0(A_1099, C_1100), u1_struct_0(A_1099)) | ~m1_subset_1(k1_yellow_0(A_1099, B_1102), u1_struct_0(A_1099)) | ~v13_waybel_0(B_1101, A_1099) | ~m1_subset_1(B_1101, k1_zfmisc_1(u1_struct_0(A_1099))) | ~r1_yellow_0(A_1099, C_1100) | ~r1_yellow_0(A_1099, B_1102) | ~r1_tarski(B_1102, C_1100) | ~l1_orders_2(A_1099))), inference(resolution, [status(thm)], [c_20, c_400])).
% 17.83/9.07  tff(c_17965, plain, (![C_1100, B_1101]: (r2_hidden(k1_yellow_0('#skF_4', C_1100), B_1101) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1101) | ~m1_subset_1(k1_yellow_0('#skF_4', C_1100), u1_struct_0('#skF_4')) | ~m1_subset_1(k1_yellow_0('#skF_4', k1_xboole_0), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1101, '#skF_4') | ~m1_subset_1(B_1101, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', C_1100) | ~r1_yellow_0('#skF_4', k1_xboole_0) | ~r1_tarski(k1_xboole_0, C_1100) | ~l1_orders_2('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_17946])).
% 17.83/9.07  tff(c_17975, plain, (![C_1103, B_1104]: (r2_hidden(k1_yellow_0('#skF_4', C_1103), B_1104) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1104) | ~m1_subset_1(k1_yellow_0('#skF_4', C_1103), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1104, '#skF_4') | ~m1_subset_1(B_1104, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', C_1103))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2, c_289, c_11727, c_93, c_17965])).
% 17.83/9.07  tff(c_17985, plain, (![B_5, B_1104]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))), B_1104) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1104) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1104, '#skF_4') | ~m1_subset_1(B_1104, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_307, c_17975])).
% 17.83/9.07  tff(c_18007, plain, (![B_5, B_1104]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))), B_1104) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1104) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1104, '#skF_4') | ~m1_subset_1(B_1104, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_17985])).
% 17.83/9.07  tff(c_27692, plain, (![B_1655, B_1656]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_1655))), B_1656) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1656) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1655), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1656, '#skF_4') | ~m1_subset_1(B_1656, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_1655))) | u1_struct_0('#skF_4')=B_1655 | ~m1_subset_1(B_1655, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_18007])).
% 17.83/9.07  tff(c_27733, plain, (![B_5, B_1656]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), B_1656) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1656) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1656, '#skF_4') | ~m1_subset_1(B_1656, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_307, c_27692])).
% 17.83/9.08  tff(c_27759, plain, (![B_5, B_1656]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), B_1656) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1656) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1656, '#skF_4') | ~m1_subset_1(B_1656, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_27733])).
% 17.83/9.08  tff(c_27761, plain, (![B_1657, B_1658]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1657), B_1658) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1658) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1657), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1658, '#skF_4') | ~m1_subset_1(B_1658, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_1657))) | u1_struct_0('#skF_4')=B_1657 | ~m1_subset_1(B_1657, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_27759])).
% 17.83/9.08  tff(c_27764, plain, (![B_1657, B_1658]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1657), B_1658) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1658) | ~v13_waybel_0(B_1658, '#skF_4') | ~m1_subset_1(B_1658, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_1657 | ~m1_subset_1(B_1657, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1657), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_27761])).
% 17.83/9.08  tff(c_27767, plain, (![B_1657, B_1658]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1657), B_1658) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1658) | ~v13_waybel_0(B_1658, '#skF_4') | ~m1_subset_1(B_1658, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_1657 | ~m1_subset_1(B_1657, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1657), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_27764])).
% 17.83/9.08  tff(c_27769, plain, (![B_1659, B_1660]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1659), B_1660) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1660) | ~v13_waybel_0(B_1660, '#skF_4') | ~m1_subset_1(B_1660, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_1659 | ~m1_subset_1(B_1659, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1659), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_27767])).
% 17.83/9.08  tff(c_27778, plain, (![B_1661, B_1662]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1661), B_1662) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1662) | ~v13_waybel_0(B_1662, '#skF_4') | ~m1_subset_1(B_1662, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_1661 | ~m1_subset_1(B_1661, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_10, c_27769])).
% 17.83/9.08  tff(c_27825, plain, (![B_1663]: (~r2_hidden(k3_yellow_0('#skF_4'), B_1663) | ~v13_waybel_0(B_1663, '#skF_4') | u1_struct_0('#skF_4')=B_1663 | ~m1_subset_1(B_1663, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_27778, c_8])).
% 17.83/9.08  tff(c_27832, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v13_waybel_0('#skF_5', '#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_46, c_27825])).
% 17.83/9.08  tff(c_27840, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_134, c_27832])).
% 17.83/9.08  tff(c_22311, plain, (![B_1421, B_1422]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_1421))), B_1422) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1422) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1421), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1422, '#skF_4') | ~m1_subset_1(B_1422, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_1421))) | u1_struct_0('#skF_4')=B_1421 | ~m1_subset_1(B_1421, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_18007])).
% 17.83/9.08  tff(c_22338, plain, (![B_5, B_1422]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), B_1422) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1422) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1422, '#skF_4') | ~m1_subset_1(B_1422, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_307, c_22311])).
% 17.83/9.08  tff(c_22355, plain, (![B_5, B_1422]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), B_1422) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1422) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1422, '#skF_4') | ~m1_subset_1(B_1422, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_22338])).
% 17.83/9.08  tff(c_22357, plain, (![B_1423, B_1424]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1423), B_1424) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1424) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1423), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1424, '#skF_4') | ~m1_subset_1(B_1424, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_1423))) | u1_struct_0('#skF_4')=B_1423 | ~m1_subset_1(B_1423, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_22355])).
% 17.83/9.08  tff(c_22360, plain, (![B_1423, B_1424]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1423), B_1424) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1424) | ~v13_waybel_0(B_1424, '#skF_4') | ~m1_subset_1(B_1424, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_1423 | ~m1_subset_1(B_1423, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1423), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_22357])).
% 17.83/9.08  tff(c_22363, plain, (![B_1423, B_1424]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1423), B_1424) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1424) | ~v13_waybel_0(B_1424, '#skF_4') | ~m1_subset_1(B_1424, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_1423 | ~m1_subset_1(B_1423, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1423), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_22360])).
% 17.83/9.08  tff(c_22365, plain, (![B_1425, B_1426]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1425), B_1426) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1426) | ~v13_waybel_0(B_1426, '#skF_4') | ~m1_subset_1(B_1426, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_1425 | ~m1_subset_1(B_1425, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1425), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_22363])).
% 17.83/9.08  tff(c_22374, plain, (![B_1427, B_1428]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1427), B_1428) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1428) | ~v13_waybel_0(B_1428, '#skF_4') | ~m1_subset_1(B_1428, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_1427 | ~m1_subset_1(B_1427, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_10, c_22365])).
% 17.83/9.08  tff(c_22398, plain, (![B_1429]: (~r2_hidden(k3_yellow_0('#skF_4'), B_1429) | ~v13_waybel_0(B_1429, '#skF_4') | u1_struct_0('#skF_4')=B_1429 | ~m1_subset_1(B_1429, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_22374, c_8])).
% 17.83/9.08  tff(c_22405, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v13_waybel_0('#skF_5', '#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_46, c_22398])).
% 17.83/9.08  tff(c_22413, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_134, c_22405])).
% 17.83/9.08  tff(c_20376, plain, (![B_1278, B_1279]: (r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_1278))), B_1279) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1279) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1278), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1279, '#skF_4') | ~m1_subset_1(B_1279, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_1278))) | u1_struct_0('#skF_4')=B_1278 | ~m1_subset_1(B_1278, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_18007])).
% 17.83/9.08  tff(c_20403, plain, (![B_5, B_1279]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), B_1279) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1279) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1279, '#skF_4') | ~m1_subset_1(B_1279, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_307, c_20376])).
% 17.83/9.08  tff(c_20420, plain, (![B_5, B_1279]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_5), B_1279) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1279) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_5), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1279, '#skF_4') | ~m1_subset_1(B_1279, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_5))) | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_20403])).
% 17.83/9.08  tff(c_20422, plain, (![B_1280, B_1281]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1280), B_1281) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1281) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1280), u1_struct_0('#skF_4')) | ~v13_waybel_0(B_1281, '#skF_4') | ~m1_subset_1(B_1281, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(u1_struct_0('#skF_4'), B_1280))) | u1_struct_0('#skF_4')=B_1280 | ~m1_subset_1(B_1280, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_20420])).
% 17.83/9.08  tff(c_20425, plain, (![B_1280, B_1281]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1280), B_1281) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1281) | ~v13_waybel_0(B_1281, '#skF_4') | ~m1_subset_1(B_1281, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_1280 | ~m1_subset_1(B_1280, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1280), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_20422])).
% 17.83/9.08  tff(c_20428, plain, (![B_1280, B_1281]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1280), B_1281) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1281) | ~v13_waybel_0(B_1281, '#skF_4') | ~m1_subset_1(B_1281, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_1280 | ~m1_subset_1(B_1280, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1280), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_20425])).
% 17.83/9.08  tff(c_20430, plain, (![B_1282, B_1283]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1282), B_1283) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1283) | ~v13_waybel_0(B_1283, '#skF_4') | ~m1_subset_1(B_1283, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_1282 | ~m1_subset_1(B_1282, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), B_1282), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_20428])).
% 17.83/9.08  tff(c_20439, plain, (![B_1284, B_1285]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_1284), B_1285) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1285) | ~v13_waybel_0(B_1285, '#skF_4') | ~m1_subset_1(B_1285, k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')=B_1284 | ~m1_subset_1(B_1284, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_10, c_20430])).
% 17.83/9.08  tff(c_20469, plain, (![B_1286]: (~r2_hidden(k3_yellow_0('#skF_4'), B_1286) | ~v13_waybel_0(B_1286, '#skF_4') | u1_struct_0('#skF_4')=B_1286 | ~m1_subset_1(B_1286, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_20439, c_8])).
% 17.83/9.08  tff(c_20476, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v13_waybel_0('#skF_5', '#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_46, c_20469])).
% 17.83/9.08  tff(c_20484, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_134, c_20476])).
% 17.83/9.08  tff(c_18018, plain, (![C_1105, B_1106]: (r2_hidden(k1_yellow_0('#skF_4', C_1105), B_1106) | ~r2_hidden(k3_yellow_0('#skF_4'), B_1106) | ~v13_waybel_0(B_1106, '#skF_4') | ~m1_subset_1(B_1106, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_yellow_0('#skF_4', C_1105) | ~r2_hidden(k1_yellow_0('#skF_4', C_1105), '#skF_5'))), inference(resolution, [status(thm)], [c_157, c_17975])).
% 17.83/9.08  tff(c_18031, plain, (![C_1105]: (r2_hidden(k1_yellow_0('#skF_4', C_1105), u1_struct_0('#skF_4')) | ~r2_hidden(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | ~v13_waybel_0(u1_struct_0('#skF_4'), '#skF_4') | ~r1_yellow_0('#skF_4', C_1105) | ~r2_hidden(k1_yellow_0('#skF_4', C_1105), '#skF_5'))), inference(resolution, [status(thm)], [c_73, c_18018])).
% 17.83/9.08  tff(c_18032, plain, (~v13_waybel_0(u1_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_18031])).
% 17.83/9.08  tff(c_20568, plain, (~v13_waybel_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20484, c_18032])).
% 17.83/9.08  tff(c_20599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_20568])).
% 17.83/9.08  tff(c_20600, plain, (![C_1105]: (~r2_hidden(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4')) | r2_hidden(k1_yellow_0('#skF_4', C_1105), u1_struct_0('#skF_4')) | ~r1_yellow_0('#skF_4', C_1105) | ~r2_hidden(k1_yellow_0('#skF_4', C_1105), '#skF_5'))), inference(splitRight, [status(thm)], [c_18031])).
% 17.83/9.08  tff(c_20606, plain, (~r2_hidden(k3_yellow_0('#skF_4'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_20600])).
% 17.83/9.08  tff(c_22477, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22413, c_20606])).
% 17.83/9.08  tff(c_22509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_22477])).
% 17.83/9.08  tff(c_22518, plain, (![C_1432]: (r2_hidden(k1_yellow_0('#skF_4', C_1432), u1_struct_0('#skF_4')) | ~r1_yellow_0('#skF_4', C_1432) | ~r2_hidden(k1_yellow_0('#skF_4', C_1432), '#skF_5'))), inference(splitRight, [status(thm)], [c_20600])).
% 17.83/9.08  tff(c_22603, plain, (![A_1433]: (r2_hidden(A_1433, u1_struct_0('#skF_4')) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', A_1433)) | ~r2_hidden(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', A_1433)), '#skF_5') | ~r2_hidden(A_1433, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_22518])).
% 17.83/9.08  tff(c_22651, plain, (![A_1434]: (r2_hidden(A_1434, u1_struct_0('#skF_4')) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', A_1434)) | ~r2_hidden(A_1434, '#skF_5') | ~r2_hidden(A_1434, '#skF_5') | ~r2_hidden(A_1434, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_22603])).
% 17.83/9.08  tff(c_22769, plain, (![A_1439]: (u1_struct_0('#skF_4')=A_1439 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_1439)) | ~r1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_1'(A_1439, u1_struct_0('#skF_4')))) | ~r2_hidden('#skF_1'(A_1439, u1_struct_0('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_22651, c_8])).
% 17.83/9.08  tff(c_22772, plain, (![A_1439]: (u1_struct_0('#skF_4')=A_1439 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_1439)) | ~r2_hidden('#skF_1'(A_1439, u1_struct_0('#skF_4')), '#skF_5') | ~m1_subset_1('#skF_1'(A_1439, u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_22769])).
% 17.83/9.08  tff(c_22775, plain, (![A_1439]: (u1_struct_0('#skF_4')=A_1439 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_1439)) | ~r2_hidden('#skF_1'(A_1439, u1_struct_0('#skF_4')), '#skF_5') | ~m1_subset_1('#skF_1'(A_1439, u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_22772])).
% 17.83/9.08  tff(c_22777, plain, (![A_1440]: (u1_struct_0('#skF_4')=A_1440 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_1440)) | ~r2_hidden('#skF_1'(A_1440, u1_struct_0('#skF_4')), '#skF_5') | ~m1_subset_1('#skF_1'(A_1440, u1_struct_0('#skF_4')), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_22775])).
% 17.83/9.08  tff(c_22790, plain, (![A_1441]: (u1_struct_0('#skF_4')=A_1441 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_1441)) | ~r2_hidden('#skF_1'(A_1441, u1_struct_0('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_157, c_22777])).
% 17.83/9.08  tff(c_22793, plain, (![A_1441]: (u1_struct_0('#skF_4')=A_1441 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_1441)) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_1'(A_1441, u1_struct_0('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_12, c_22790])).
% 17.83/9.08  tff(c_22797, plain, (![A_1442]: (u1_struct_0('#skF_4')=A_1442 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_1442)) | ~m1_subset_1('#skF_1'(A_1442, u1_struct_0('#skF_4')), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_52, c_22793])).
% 17.83/9.08  tff(c_22802, plain, (u1_struct_0('#skF_4')='#skF_5' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_22797])).
% 17.83/9.08  tff(c_22803, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_22802])).
% 17.83/9.08  tff(c_27946, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_27840, c_22803])).
% 17.83/9.08  tff(c_27988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_27946])).
% 17.83/9.08  tff(c_27989, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_22802])).
% 17.83/9.08  tff(c_28066, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_27989, c_206])).
% 17.83/9.08  tff(c_28074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_28066])).
% 17.83/9.08  tff(c_28077, plain, (![A_1666]: (u1_struct_0('#skF_4')=A_1666 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_1666)) | ~r2_hidden('#skF_1'(A_1666, u1_struct_0('#skF_4')), '#skF_5'))), inference(splitRight, [status(thm)], [c_200])).
% 17.83/9.08  tff(c_28080, plain, (![A_1666]: (u1_struct_0('#skF_4')=A_1666 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_1666)) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_1'(A_1666, u1_struct_0('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_12, c_28077])).
% 17.83/9.08  tff(c_28084, plain, (![A_1667]: (u1_struct_0('#skF_4')=A_1667 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_1667)) | ~m1_subset_1('#skF_1'(A_1667, u1_struct_0('#skF_4')), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_52, c_28080])).
% 17.83/9.08  tff(c_28089, plain, (u1_struct_0('#skF_4')='#skF_5' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_28084])).
% 17.83/9.08  tff(c_28090, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_28089])).
% 17.83/9.08  tff(c_33078, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32978, c_28090])).
% 17.83/9.08  tff(c_33090, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_33078])).
% 17.83/9.08  tff(c_33091, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_28089])).
% 17.83/9.08  tff(c_135, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_66])).
% 17.83/9.08  tff(c_33111, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_33091, c_135])).
% 17.83/9.08  tff(c_33114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_33111])).
% 17.83/9.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.83/9.08  
% 17.83/9.08  Inference rules
% 17.83/9.08  ----------------------
% 17.83/9.08  #Ref     : 0
% 17.83/9.08  #Sup     : 6159
% 17.83/9.08  #Fact    : 0
% 17.83/9.08  #Define  : 0
% 17.83/9.08  #Split   : 45
% 17.83/9.08  #Chain   : 0
% 17.83/9.08  #Close   : 0
% 17.83/9.08  
% 17.83/9.08  Ordering : KBO
% 17.83/9.08  
% 17.83/9.08  Simplification rules
% 17.83/9.08  ----------------------
% 17.83/9.08  #Subsume      : 2116
% 17.83/9.08  #Demod        : 17719
% 17.83/9.08  #Tautology    : 1696
% 17.83/9.08  #SimpNegUnit  : 2082
% 17.83/9.08  #BackRed      : 988
% 17.83/9.08  
% 17.83/9.08  #Partial instantiations: 0
% 17.83/9.08  #Strategies tried      : 1
% 17.83/9.08  
% 17.83/9.08  Timing (in seconds)
% 17.83/9.08  ----------------------
% 17.83/9.08  Preprocessing        : 0.55
% 17.83/9.08  Parsing              : 0.28
% 17.83/9.08  CNF conversion       : 0.04
% 17.83/9.08  Main loop            : 7.54
% 17.83/9.08  Inferencing          : 2.08
% 17.83/9.08  Reduction            : 2.88
% 17.83/9.08  Demodulation         : 2.12
% 17.83/9.08  BG Simplification    : 0.22
% 17.83/9.08  Subsumption          : 1.99
% 17.83/9.08  Abstraction          : 0.35
% 17.83/9.08  MUC search           : 0.00
% 17.83/9.08  Cooper               : 0.00
% 17.83/9.08  Total                : 8.21
% 17.83/9.08  Index Insertion      : 0.00
% 17.83/9.08  Index Deletion       : 0.00
% 17.83/9.08  Index Matching       : 0.00
% 17.83/9.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
