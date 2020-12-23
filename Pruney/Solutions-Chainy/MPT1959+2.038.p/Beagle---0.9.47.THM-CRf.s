%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:02 EST 2020

% Result     : Theorem 19.06s
% Output     : CNFRefutation 19.24s
% Verified   : 
% Statistics : Number of formulae       :  372 (3681 expanded)
%              Number of leaves         :   44 (1313 expanded)
%              Depth                    :   33
%              Number of atoms          : 1544 (16994 expanded)
%              Number of equality atoms :  168 ( 943 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_42,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_159,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_123,axiom,(
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

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_86,axiom,(
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

tff(f_58,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( ( r1_tarski(B,C)
            & r1_yellow_0(A,B)
            & r1_yellow_0(A,C) )
         => r1_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow_0)).

tff(f_105,axiom,(
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

tff(c_8,plain,(
    ! [A_5] : ~ v1_subset_1('#skF_2'(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1('#skF_2'(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_144,plain,(
    ! [B_66,A_67] :
      ( v1_subset_1(B_66,A_67)
      | B_66 = A_67
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_150,plain,(
    ! [A_5] :
      ( v1_subset_1('#skF_2'(A_5),A_5)
      | '#skF_2'(A_5) = A_5 ) ),
    inference(resolution,[status(thm)],[c_10,c_144])).

tff(c_155,plain,(
    ! [A_5] : '#skF_2'(A_5) = A_5 ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_150])).

tff(c_157,plain,(
    ! [A_5] : ~ v1_subset_1(A_5,A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_8])).

tff(c_156,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_10])).

tff(c_48,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_66,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_88,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_72,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_89,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_92,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_89])).

tff(c_95,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_92])).

tff(c_54,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_96,plain,(
    ! [B_59,A_60] :
      ( v1_subset_1(B_59,A_60)
      | B_59 = A_60
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_99,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_96])).

tff(c_105,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_99])).

tff(c_18,plain,(
    ! [A_13] :
      ( m1_subset_1(k3_yellow_0(A_13),u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_130,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_18])).

tff(c_134,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_130])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_134])).

tff(c_137,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_137])).

tff(c_140,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1('#skF_1'(A_2,B_3),A_2)
      | B_3 = A_2
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_62,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_60,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_58,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_40,plain,(
    ! [A_45,B_47] :
      ( r1_yellow_0(A_45,k5_waybel_0(A_45,B_47))
      | ~ m1_subset_1(B_47,u1_struct_0(A_45))
      | ~ l1_orders_2(A_45)
      | ~ v5_orders_2(A_45)
      | ~ v4_orders_2(A_45)
      | ~ v3_orders_2(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_26184,plain,(
    ! [A_1630,B_1631] :
      ( k1_yellow_0(A_1630,k5_waybel_0(A_1630,B_1631)) = B_1631
      | ~ m1_subset_1(B_1631,u1_struct_0(A_1630))
      | ~ l1_orders_2(A_1630)
      | ~ v5_orders_2(A_1630)
      | ~ v4_orders_2(A_1630)
      | ~ v3_orders_2(A_1630)
      | v2_struct_0(A_1630) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_26201,plain,(
    ! [A_1630,B_3] :
      ( k1_yellow_0(A_1630,k5_waybel_0(A_1630,'#skF_1'(u1_struct_0(A_1630),B_3))) = '#skF_1'(u1_struct_0(A_1630),B_3)
      | ~ l1_orders_2(A_1630)
      | ~ v5_orders_2(A_1630)
      | ~ v4_orders_2(A_1630)
      | ~ v3_orders_2(A_1630)
      | v2_struct_0(A_1630)
      | u1_struct_0(A_1630) = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1630))) ) ),
    inference(resolution,[status(thm)],[c_6,c_26184])).

tff(c_167,plain,(
    ! [A_69,C_70,B_71] :
      ( m1_subset_1(A_69,C_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(C_70))
      | ~ r2_hidden(A_69,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_170,plain,(
    ! [A_69] :
      ( m1_subset_1(A_69,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_69,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_167])).

tff(c_56,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_24,plain,(
    ! [A_19] :
      ( r1_yellow_0(A_19,k1_xboole_0)
      | ~ l1_orders_2(A_19)
      | ~ v1_yellow_0(A_19)
      | ~ v5_orders_2(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_77,plain,(
    ! [A_55] :
      ( k1_yellow_0(A_55,k1_xboole_0) = k3_yellow_0(A_55)
      | ~ l1_orders_2(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_81,plain,(
    k1_yellow_0('#skF_5',k1_xboole_0) = k3_yellow_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_77])).

tff(c_26162,plain,(
    ! [A_1627,B_1628,C_1629] :
      ( r1_orders_2(A_1627,k1_yellow_0(A_1627,B_1628),k1_yellow_0(A_1627,C_1629))
      | ~ r1_yellow_0(A_1627,C_1629)
      | ~ r1_yellow_0(A_1627,B_1628)
      | ~ r1_tarski(B_1628,C_1629)
      | ~ l1_orders_2(A_1627) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26165,plain,(
    ! [C_1629] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),k1_yellow_0('#skF_5',C_1629))
      | ~ r1_yellow_0('#skF_5',C_1629)
      | ~ r1_yellow_0('#skF_5',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,C_1629)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_26162])).

tff(c_26170,plain,(
    ! [C_1629] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),k1_yellow_0('#skF_5',C_1629))
      | ~ r1_yellow_0('#skF_5',C_1629)
      | ~ r1_yellow_0('#skF_5',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2,c_26165])).

tff(c_26173,plain,(
    ~ r1_yellow_0('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_26170])).

tff(c_26176,plain,
    ( ~ l1_orders_2('#skF_5')
    | ~ v1_yellow_0('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_26173])).

tff(c_26179,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_26176])).

tff(c_26181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_26179])).

tff(c_26182,plain,(
    ! [C_1629] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),k1_yellow_0('#skF_5',C_1629))
      | ~ r1_yellow_0('#skF_5',C_1629) ) ),
    inference(splitRight,[status(thm)],[c_26170])).

tff(c_26294,plain,(
    ! [D_1640,B_1641,A_1642,C_1643] :
      ( r2_hidden(D_1640,B_1641)
      | ~ r1_orders_2(A_1642,C_1643,D_1640)
      | ~ r2_hidden(C_1643,B_1641)
      | ~ m1_subset_1(D_1640,u1_struct_0(A_1642))
      | ~ m1_subset_1(C_1643,u1_struct_0(A_1642))
      | ~ v13_waybel_0(B_1641,A_1642)
      | ~ m1_subset_1(B_1641,k1_zfmisc_1(u1_struct_0(A_1642)))
      | ~ l1_orders_2(A_1642) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_26304,plain,(
    ! [C_1629,B_1641] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_1629),B_1641)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1641)
      | ~ m1_subset_1(k1_yellow_0('#skF_5',C_1629),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1641,'#skF_5')
      | ~ m1_subset_1(B_1641,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ r1_yellow_0('#skF_5',C_1629) ) ),
    inference(resolution,[status(thm)],[c_26182,c_26294])).

tff(c_26323,plain,(
    ! [C_1629,B_1641] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_1629),B_1641)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1641)
      | ~ m1_subset_1(k1_yellow_0('#skF_5',C_1629),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1641,'#skF_5')
      | ~ m1_subset_1(B_1641,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',C_1629) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_26304])).

tff(c_26642,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_26323])).

tff(c_26645,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_170,c_26642])).

tff(c_26652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_26645])).

tff(c_26777,plain,(
    ! [C_1666,B_1667] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_1666),B_1667)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1667)
      | ~ m1_subset_1(k1_yellow_0('#skF_5',C_1666),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1667,'#skF_5')
      | ~ m1_subset_1(B_1667,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',C_1666) ) ),
    inference(splitRight,[status(thm)],[c_26323])).

tff(c_26782,plain,(
    ! [B_3,B_1667] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3))),B_1667)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1667)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1667,'#skF_5')
      | ~ m1_subset_1(B_1667,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26201,c_26777])).

tff(c_26802,plain,(
    ! [B_3,B_1667] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3))),B_1667)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1667)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1667,'#skF_5')
      | ~ m1_subset_1(B_1667,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_26782])).

tff(c_29628,plain,(
    ! [B_1811,B_1812] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_1811))),B_1812)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1812)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1811),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1812,'#skF_5')
      | ~ m1_subset_1(B_1812,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_1811)))
      | u1_struct_0('#skF_5') = B_1811
      | ~ m1_subset_1(B_1811,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_26802])).

tff(c_29659,plain,(
    ! [B_3,B_1812] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_3),B_1812)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1812)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1812,'#skF_5')
      | ~ m1_subset_1(B_1812,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26201,c_29628])).

tff(c_29680,plain,(
    ! [B_3,B_1812] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_3),B_1812)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1812)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1812,'#skF_5')
      | ~ m1_subset_1(B_1812,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_29659])).

tff(c_29682,plain,(
    ! [B_1813,B_1814] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1813),B_1814)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1814)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1813),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1814,'#skF_5')
      | ~ m1_subset_1(B_1814,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_1813)))
      | u1_struct_0('#skF_5') = B_1813
      | ~ m1_subset_1(B_1813,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_29680])).

tff(c_29685,plain,(
    ! [B_1813,B_1814] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1813),B_1814)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1814)
      | ~ v13_waybel_0(B_1814,'#skF_5')
      | ~ m1_subset_1(B_1814,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_1813
      | ~ m1_subset_1(B_1813,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1813),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_29682])).

tff(c_29688,plain,(
    ! [B_1813,B_1814] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1813),B_1814)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1814)
      | ~ v13_waybel_0(B_1814,'#skF_5')
      | ~ m1_subset_1(B_1814,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_1813
      | ~ m1_subset_1(B_1813,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1813),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_29685])).

tff(c_29690,plain,(
    ! [B_1815,B_1816] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1815),B_1816)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1816)
      | ~ v13_waybel_0(B_1816,'#skF_5')
      | ~ m1_subset_1(B_1816,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_1815
      | ~ m1_subset_1(B_1815,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1815),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_29688])).

tff(c_29699,plain,(
    ! [B_1817,B_1818] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1817),B_1818)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1818)
      | ~ v13_waybel_0(B_1818,'#skF_5')
      | ~ m1_subset_1(B_1818,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_1817
      | ~ m1_subset_1(B_1817,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_29690])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( ~ r2_hidden('#skF_1'(A_2,B_3),B_3)
      | B_3 = A_2
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_29731,plain,(
    ! [B_1819] :
      ( ~ r2_hidden(k3_yellow_0('#skF_5'),B_1819)
      | ~ v13_waybel_0(B_1819,'#skF_5')
      | u1_struct_0('#skF_5') = B_1819
      | ~ m1_subset_1(B_1819,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_29699,c_4])).

tff(c_29742,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v13_waybel_0('#skF_6','#skF_5')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_29731])).

tff(c_29750,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_140,c_29742])).

tff(c_320,plain,(
    ! [A_110,B_111] :
      ( k1_yellow_0(A_110,k5_waybel_0(A_110,B_111)) = B_111
      | ~ m1_subset_1(B_111,u1_struct_0(A_110))
      | ~ l1_orders_2(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v4_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_337,plain,(
    ! [A_110,B_3] :
      ( k1_yellow_0(A_110,k5_waybel_0(A_110,'#skF_1'(u1_struct_0(A_110),B_3))) = '#skF_1'(u1_struct_0(A_110),B_3)
      | ~ l1_orders_2(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v4_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110)
      | u1_struct_0(A_110) = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_110))) ) ),
    inference(resolution,[status(thm)],[c_6,c_320])).

tff(c_292,plain,(
    ! [A_106,B_107,C_108] :
      ( r1_orders_2(A_106,k1_yellow_0(A_106,B_107),k1_yellow_0(A_106,C_108))
      | ~ r1_yellow_0(A_106,C_108)
      | ~ r1_yellow_0(A_106,B_107)
      | ~ r1_tarski(B_107,C_108)
      | ~ l1_orders_2(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_295,plain,(
    ! [C_108] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),k1_yellow_0('#skF_5',C_108))
      | ~ r1_yellow_0('#skF_5',C_108)
      | ~ r1_yellow_0('#skF_5',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,C_108)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_292])).

tff(c_300,plain,(
    ! [C_108] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),k1_yellow_0('#skF_5',C_108))
      | ~ r1_yellow_0('#skF_5',C_108)
      | ~ r1_yellow_0('#skF_5',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2,c_295])).

tff(c_303,plain,(
    ~ r1_yellow_0('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_306,plain,
    ( ~ l1_orders_2('#skF_5')
    | ~ v1_yellow_0('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_303])).

tff(c_309,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_306])).

tff(c_311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_309])).

tff(c_313,plain,(
    r1_yellow_0('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_312,plain,(
    ! [C_108] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),k1_yellow_0('#skF_5',C_108))
      | ~ r1_yellow_0('#skF_5',C_108) ) ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_450,plain,(
    ! [D_124,B_125,A_126,C_127] :
      ( r2_hidden(D_124,B_125)
      | ~ r1_orders_2(A_126,C_127,D_124)
      | ~ r2_hidden(C_127,B_125)
      | ~ m1_subset_1(D_124,u1_struct_0(A_126))
      | ~ m1_subset_1(C_127,u1_struct_0(A_126))
      | ~ v13_waybel_0(B_125,A_126)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_orders_2(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_462,plain,(
    ! [C_108,B_125] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_108),B_125)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_125)
      | ~ m1_subset_1(k1_yellow_0('#skF_5',C_108),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_125,'#skF_5')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ r1_yellow_0('#skF_5',C_108) ) ),
    inference(resolution,[status(thm)],[c_312,c_450])).

tff(c_484,plain,(
    ! [C_108,B_125] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_108),B_125)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_125)
      | ~ m1_subset_1(k1_yellow_0('#skF_5',C_108),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_125,'#skF_5')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',C_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_462])).

tff(c_775,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_484])).

tff(c_784,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_170,c_775])).

tff(c_791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_784])).

tff(c_907,plain,(
    ! [C_144,B_145] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_144),B_145)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_145)
      | ~ m1_subset_1(k1_yellow_0('#skF_5',C_144),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_145,'#skF_5')
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',C_144) ) ),
    inference(splitRight,[status(thm)],[c_484])).

tff(c_912,plain,(
    ! [B_3,B_145] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3))),B_145)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_145)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_145,'#skF_5')
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_907])).

tff(c_932,plain,(
    ! [B_3,B_145] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3))),B_145)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_145)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_145,'#skF_5')
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_912])).

tff(c_6405,plain,(
    ! [B_461,B_462] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_461))),B_462)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_462)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_461),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_462,'#skF_5')
      | ~ m1_subset_1(B_462,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_461)))
      | u1_struct_0('#skF_5') = B_461
      | ~ m1_subset_1(B_461,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_932])).

tff(c_6440,plain,(
    ! [B_3,B_462] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_3),B_462)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_462)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_462,'#skF_5')
      | ~ m1_subset_1(B_462,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_6405])).

tff(c_6463,plain,(
    ! [B_3,B_462] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_3),B_462)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_462)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_462,'#skF_5')
      | ~ m1_subset_1(B_462,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_6440])).

tff(c_6465,plain,(
    ! [B_463,B_464] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_463),B_464)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_464)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_463),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_464,'#skF_5')
      | ~ m1_subset_1(B_464,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_463)))
      | u1_struct_0('#skF_5') = B_463
      | ~ m1_subset_1(B_463,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6463])).

tff(c_6468,plain,(
    ! [B_463,B_464] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_463),B_464)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_464)
      | ~ v13_waybel_0(B_464,'#skF_5')
      | ~ m1_subset_1(B_464,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_463
      | ~ m1_subset_1(B_463,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_463),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_6465])).

tff(c_6471,plain,(
    ! [B_463,B_464] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_463),B_464)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_464)
      | ~ v13_waybel_0(B_464,'#skF_5')
      | ~ m1_subset_1(B_464,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_463
      | ~ m1_subset_1(B_463,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_463),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_6468])).

tff(c_6473,plain,(
    ! [B_465,B_466] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_465),B_466)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_466)
      | ~ v13_waybel_0(B_466,'#skF_5')
      | ~ m1_subset_1(B_466,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_465
      | ~ m1_subset_1(B_465,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_465),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6471])).

tff(c_6482,plain,(
    ! [B_467,B_468] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_467),B_468)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_468)
      | ~ v13_waybel_0(B_468,'#skF_5')
      | ~ m1_subset_1(B_468,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_467
      | ~ m1_subset_1(B_467,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_6473])).

tff(c_6523,plain,(
    ! [B_469] :
      ( ~ r2_hidden(k3_yellow_0('#skF_5'),B_469)
      | ~ v13_waybel_0(B_469,'#skF_5')
      | u1_struct_0('#skF_5') = B_469
      | ~ m1_subset_1(B_469,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_6482,c_4])).

tff(c_6534,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v13_waybel_0('#skF_6','#skF_5')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_6523])).

tff(c_6542,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_140,c_6534])).

tff(c_331,plain,(
    ! [A_69] :
      ( k1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_69)) = A_69
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(A_69,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_170,c_320])).

tff(c_340,plain,(
    ! [A_69] :
      ( k1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_69)) = A_69
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(A_69,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_331])).

tff(c_341,plain,(
    ! [A_69] :
      ( k1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_69)) = A_69
      | ~ r2_hidden(A_69,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_340])).

tff(c_2316,plain,(
    ! [B_266,B_267] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_266))),B_267)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_267)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_266),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_267,'#skF_5')
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_266)))
      | u1_struct_0('#skF_5') = B_266
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_932])).

tff(c_2343,plain,(
    ! [B_3,B_267] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_3),B_267)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_267)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_267,'#skF_5')
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_2316])).

tff(c_2360,plain,(
    ! [B_3,B_267] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_3),B_267)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_267)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_267,'#skF_5')
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_2343])).

tff(c_2362,plain,(
    ! [B_268,B_269] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_268),B_269)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_269)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_268),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_269,'#skF_5')
      | ~ m1_subset_1(B_269,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_268)))
      | u1_struct_0('#skF_5') = B_268
      | ~ m1_subset_1(B_268,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2360])).

tff(c_2365,plain,(
    ! [B_268,B_269] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_268),B_269)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_269)
      | ~ v13_waybel_0(B_269,'#skF_5')
      | ~ m1_subset_1(B_269,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_268
      | ~ m1_subset_1(B_268,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_268),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_2362])).

tff(c_2368,plain,(
    ! [B_268,B_269] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_268),B_269)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_269)
      | ~ v13_waybel_0(B_269,'#skF_5')
      | ~ m1_subset_1(B_269,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_268
      | ~ m1_subset_1(B_268,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_268),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_2365])).

tff(c_2370,plain,(
    ! [B_270,B_271] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_270),B_271)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_271)
      | ~ v13_waybel_0(B_271,'#skF_5')
      | ~ m1_subset_1(B_271,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_270
      | ~ m1_subset_1(B_270,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_270),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2368])).

tff(c_2379,plain,(
    ! [B_272,B_273] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_272),B_273)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_273)
      | ~ v13_waybel_0(B_273,'#skF_5')
      | ~ m1_subset_1(B_273,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_272
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_2370])).

tff(c_2406,plain,(
    ! [B_274] :
      ( ~ r2_hidden(k3_yellow_0('#skF_5'),B_274)
      | ~ v13_waybel_0(B_274,'#skF_5')
      | u1_struct_0('#skF_5') = B_274
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_2379,c_4])).

tff(c_2417,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v13_waybel_0('#skF_6','#skF_5')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_2406])).

tff(c_2424,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_140,c_2417])).

tff(c_36,plain,(
    ! [A_20,B_34] :
      ( m1_subset_1('#skF_3'(A_20,B_34),u1_struct_0(A_20))
      | v13_waybel_0(B_34,A_20)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_211,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_3'(A_83,B_84),B_84)
      | v13_waybel_0(B_84,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_orders_2(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_239,plain,(
    ! [A_87] :
      ( r2_hidden('#skF_3'(A_87,u1_struct_0(A_87)),u1_struct_0(A_87))
      | v13_waybel_0(u1_struct_0(A_87),A_87)
      | ~ l1_orders_2(A_87) ) ),
    inference(resolution,[status(thm)],[c_156,c_211])).

tff(c_172,plain,(
    ! [A_73] : m1_subset_1(A_73,k1_zfmisc_1(A_73)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_10])).

tff(c_14,plain,(
    ! [A_9,C_11,B_10] :
      ( m1_subset_1(A_9,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_178,plain,(
    ! [A_9,A_73] :
      ( m1_subset_1(A_9,A_73)
      | ~ r2_hidden(A_9,A_73) ) ),
    inference(resolution,[status(thm)],[c_172,c_14])).

tff(c_243,plain,(
    ! [A_87] :
      ( m1_subset_1('#skF_3'(A_87,u1_struct_0(A_87)),u1_struct_0(A_87))
      | v13_waybel_0(u1_struct_0(A_87),A_87)
      | ~ l1_orders_2(A_87) ) ),
    inference(resolution,[status(thm)],[c_239,c_178])).

tff(c_508,plain,(
    ! [A_130] :
      ( k1_yellow_0(A_130,k5_waybel_0(A_130,'#skF_3'(A_130,u1_struct_0(A_130)))) = '#skF_3'(A_130,u1_struct_0(A_130))
      | ~ v5_orders_2(A_130)
      | ~ v4_orders_2(A_130)
      | ~ v3_orders_2(A_130)
      | v2_struct_0(A_130)
      | v13_waybel_0(u1_struct_0(A_130),A_130)
      | ~ l1_orders_2(A_130) ) ),
    inference(resolution,[status(thm)],[c_243,c_320])).

tff(c_531,plain,
    ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),'#skF_3'('#skF_5',u1_struct_0('#skF_5')))
    | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_3'('#skF_5',u1_struct_0('#skF_5'))))
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_312])).

tff(c_560,plain,
    ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),'#skF_3'('#skF_5',u1_struct_0('#skF_5')))
    | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_3'('#skF_5',u1_struct_0('#skF_5'))))
    | v2_struct_0('#skF_5')
    | v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_62,c_60,c_58,c_531])).

tff(c_561,plain,
    ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),'#skF_3'('#skF_5',u1_struct_0('#skF_5')))
    | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_3'('#skF_5',u1_struct_0('#skF_5'))))
    | v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_560])).

tff(c_567,plain,(
    ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_3'('#skF_5',u1_struct_0('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_561])).

tff(c_590,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_5',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_567])).

tff(c_593,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_5',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_590])).

tff(c_594,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5',u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_593])).

tff(c_597,plain,
    ( v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5')
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_594])).

tff(c_606,plain,(
    v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_156,c_597])).

tff(c_955,plain,(
    ! [C_148,B_149] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_148),B_149)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_149)
      | ~ v13_waybel_0(B_149,'#skF_5')
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',C_148)
      | ~ r2_hidden(k1_yellow_0('#skF_5',C_148),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_170,c_907])).

tff(c_961,plain,(
    ! [C_148] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_148),u1_struct_0('#skF_5'))
      | ~ r2_hidden(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5')
      | ~ r1_yellow_0('#skF_5',C_148)
      | ~ r2_hidden(k1_yellow_0('#skF_5',C_148),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_156,c_955])).

tff(c_967,plain,(
    ! [C_148] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_148),u1_struct_0('#skF_5'))
      | ~ r2_hidden(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',C_148)
      | ~ r2_hidden(k1_yellow_0('#skF_5',C_148),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_961])).

tff(c_971,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_967])).

tff(c_2464,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2424,c_971])).

tff(c_2480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_2464])).

tff(c_2501,plain,(
    ! [C_278] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_278),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',C_278)
      | ~ r2_hidden(k1_yellow_0('#skF_5',C_278),'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_967])).

tff(c_2547,plain,(
    ! [A_279] :
      ( r2_hidden(A_279,u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_279))
      | ~ r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_279)),'#skF_6')
      | ~ r2_hidden(A_279,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_2501])).

tff(c_2627,plain,(
    ! [A_281] :
      ( r2_hidden(A_281,u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_281))
      | ~ r2_hidden(A_281,'#skF_6')
      | ~ r2_hidden(A_281,'#skF_6')
      | ~ r2_hidden(A_281,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_2547])).

tff(c_2663,plain,(
    ! [A_283] :
      ( u1_struct_0('#skF_5') = A_283
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_283))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(A_283,u1_struct_0('#skF_5'))))
      | ~ r2_hidden('#skF_1'(A_283,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2627,c_4])).

tff(c_2666,plain,(
    ! [A_283] :
      ( u1_struct_0('#skF_5') = A_283
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_283))
      | ~ r2_hidden('#skF_1'(A_283,u1_struct_0('#skF_5')),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_283,u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_2663])).

tff(c_2669,plain,(
    ! [A_283] :
      ( u1_struct_0('#skF_5') = A_283
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_283))
      | ~ r2_hidden('#skF_1'(A_283,u1_struct_0('#skF_5')),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_283,u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_2666])).

tff(c_2671,plain,(
    ! [A_284] :
      ( u1_struct_0('#skF_5') = A_284
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_284))
      | ~ r2_hidden('#skF_1'(A_284,u1_struct_0('#skF_5')),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_284,u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2669])).

tff(c_2684,plain,(
    ! [A_285] :
      ( u1_struct_0('#skF_5') = A_285
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_285))
      | ~ r2_hidden('#skF_1'(A_285,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_170,c_2671])).

tff(c_2687,plain,(
    ! [A_285] :
      ( u1_struct_0('#skF_5') = A_285
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_285))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1('#skF_1'(A_285,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_12,c_2684])).

tff(c_2729,plain,(
    ! [A_290] :
      ( u1_struct_0('#skF_5') = A_290
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_290))
      | ~ m1_subset_1('#skF_1'(A_290,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2687])).

tff(c_2734,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6,c_2729])).

tff(c_2735,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2734])).

tff(c_6611,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6542,c_2735])).

tff(c_6635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_6611])).

tff(c_6636,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2734])).

tff(c_204,plain,(
    ! [A_80,B_81] :
      ( ~ r2_hidden('#skF_1'(A_80,B_81),B_81)
      | B_81 = A_80
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_225,plain,(
    ! [B_85,A_86] :
      ( B_85 = A_86
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86))
      | v1_xboole_0(B_85)
      | ~ m1_subset_1('#skF_1'(A_86,B_85),B_85) ) ),
    inference(resolution,[status(thm)],[c_12,c_204])).

tff(c_238,plain,(
    ! [A_86] :
      ( u1_struct_0('#skF_5') = A_86
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_86))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_1'(A_86,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_170,c_225])).

tff(c_245,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_6659,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6636,c_245])).

tff(c_6667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_6659])).

tff(c_6668,plain,
    ( v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5')
    | r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),'#skF_3'('#skF_5',u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_561])).

tff(c_6670,plain,(
    r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),'#skF_3'('#skF_5',u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_6668])).

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
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6692,plain,(
    ! [B_34] :
      ( r2_hidden('#skF_3'('#skF_5',u1_struct_0('#skF_5')),B_34)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_34)
      | ~ m1_subset_1('#skF_3'('#skF_5',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_34,'#skF_5')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6670,c_26])).

tff(c_6695,plain,(
    ! [B_34] :
      ( r2_hidden('#skF_3'('#skF_5',u1_struct_0('#skF_5')),B_34)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_34)
      | ~ m1_subset_1('#skF_3'('#skF_5',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_34,'#skF_5')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6692])).

tff(c_6879,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6695])).

tff(c_6882,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_170,c_6879])).

tff(c_6889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_6882])).

tff(c_6891,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6695])).

tff(c_7043,plain,(
    ! [C_488,B_489] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_488),B_489)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_489)
      | ~ m1_subset_1(k1_yellow_0('#skF_5',C_488),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_489,'#skF_5')
      | ~ m1_subset_1(B_489,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',C_488) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6891,c_484])).

tff(c_7048,plain,(
    ! [B_3,B_489] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3))),B_489)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_489)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_489,'#skF_5')
      | ~ m1_subset_1(B_489,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_7043])).

tff(c_7068,plain,(
    ! [B_3,B_489] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3))),B_489)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_489)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_489,'#skF_5')
      | ~ m1_subset_1(B_489,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_7048])).

tff(c_11656,plain,(
    ! [B_764,B_765] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_764))),B_765)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_765)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_764),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_765,'#skF_5')
      | ~ m1_subset_1(B_765,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_764)))
      | u1_struct_0('#skF_5') = B_764
      | ~ m1_subset_1(B_764,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_7068])).

tff(c_11691,plain,(
    ! [B_3,B_765] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_3),B_765)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_765)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_765,'#skF_5')
      | ~ m1_subset_1(B_765,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_11656])).

tff(c_11714,plain,(
    ! [B_3,B_765] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_3),B_765)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_765)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_765,'#skF_5')
      | ~ m1_subset_1(B_765,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_11691])).

tff(c_11716,plain,(
    ! [B_766,B_767] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_766),B_767)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_767)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_766),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_767,'#skF_5')
      | ~ m1_subset_1(B_767,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_766)))
      | u1_struct_0('#skF_5') = B_766
      | ~ m1_subset_1(B_766,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11714])).

tff(c_11719,plain,(
    ! [B_766,B_767] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_766),B_767)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_767)
      | ~ v13_waybel_0(B_767,'#skF_5')
      | ~ m1_subset_1(B_767,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_766
      | ~ m1_subset_1(B_766,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_766),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_11716])).

tff(c_11722,plain,(
    ! [B_766,B_767] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_766),B_767)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_767)
      | ~ v13_waybel_0(B_767,'#skF_5')
      | ~ m1_subset_1(B_767,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_766
      | ~ m1_subset_1(B_766,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_766),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_11719])).

tff(c_11724,plain,(
    ! [B_768,B_769] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_768),B_769)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_769)
      | ~ v13_waybel_0(B_769,'#skF_5')
      | ~ m1_subset_1(B_769,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_768
      | ~ m1_subset_1(B_768,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_768),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11722])).

tff(c_11733,plain,(
    ! [B_770,B_771] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_770),B_771)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_771)
      | ~ v13_waybel_0(B_771,'#skF_5')
      | ~ m1_subset_1(B_771,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_770
      | ~ m1_subset_1(B_770,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_11724])).

tff(c_11768,plain,(
    ! [B_772] :
      ( ~ r2_hidden(k3_yellow_0('#skF_5'),B_772)
      | ~ v13_waybel_0(B_772,'#skF_5')
      | u1_struct_0('#skF_5') = B_772
      | ~ m1_subset_1(B_772,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_11733,c_4])).

tff(c_11779,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v13_waybel_0('#skF_6','#skF_5')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_11768])).

tff(c_11787,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_140,c_11779])).

tff(c_8140,plain,(
    ! [B_592,B_593] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_592))),B_593)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_593)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_592),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_593,'#skF_5')
      | ~ m1_subset_1(B_593,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_592)))
      | u1_struct_0('#skF_5') = B_592
      | ~ m1_subset_1(B_592,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_7068])).

tff(c_8163,plain,(
    ! [B_3,B_593] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_3),B_593)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_593)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_593,'#skF_5')
      | ~ m1_subset_1(B_593,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_8140])).

tff(c_8178,plain,(
    ! [B_3,B_593] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_3),B_593)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_593)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_593,'#skF_5')
      | ~ m1_subset_1(B_593,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_8163])).

tff(c_8180,plain,(
    ! [B_594,B_595] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_594),B_595)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_595)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_594),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_595,'#skF_5')
      | ~ m1_subset_1(B_595,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_594)))
      | u1_struct_0('#skF_5') = B_594
      | ~ m1_subset_1(B_594,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_8178])).

tff(c_8183,plain,(
    ! [B_594,B_595] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_594),B_595)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_595)
      | ~ v13_waybel_0(B_595,'#skF_5')
      | ~ m1_subset_1(B_595,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_594
      | ~ m1_subset_1(B_594,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_594),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_8180])).

tff(c_8186,plain,(
    ! [B_594,B_595] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_594),B_595)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_595)
      | ~ v13_waybel_0(B_595,'#skF_5')
      | ~ m1_subset_1(B_595,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_594
      | ~ m1_subset_1(B_594,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_594),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_8183])).

tff(c_8188,plain,(
    ! [B_596,B_597] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_596),B_597)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_597)
      | ~ v13_waybel_0(B_597,'#skF_5')
      | ~ m1_subset_1(B_597,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_596
      | ~ m1_subset_1(B_596,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_596),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_8186])).

tff(c_8197,plain,(
    ! [B_598,B_599] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_598),B_599)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_599)
      | ~ v13_waybel_0(B_599,'#skF_5')
      | ~ m1_subset_1(B_599,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_598
      | ~ m1_subset_1(B_598,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_8188])).

tff(c_8221,plain,(
    ! [B_600] :
      ( ~ r2_hidden(k3_yellow_0('#skF_5'),B_600)
      | ~ v13_waybel_0(B_600,'#skF_5')
      | u1_struct_0('#skF_5') = B_600
      | ~ m1_subset_1(B_600,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_8197,c_4])).

tff(c_8232,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v13_waybel_0('#skF_6','#skF_5')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_8221])).

tff(c_8239,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_140,c_8232])).

tff(c_34,plain,(
    ! [A_20,B_34] :
      ( m1_subset_1('#skF_4'(A_20,B_34),u1_struct_0(A_20))
      | v13_waybel_0(B_34,A_20)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6697,plain,(
    ! [A_473,B_474] :
      ( k1_yellow_0(A_473,k5_waybel_0(A_473,'#skF_4'(A_473,B_474))) = '#skF_4'(A_473,B_474)
      | ~ v5_orders_2(A_473)
      | ~ v4_orders_2(A_473)
      | ~ v3_orders_2(A_473)
      | v2_struct_0(A_473)
      | v13_waybel_0(B_474,A_473)
      | ~ m1_subset_1(B_474,k1_zfmisc_1(u1_struct_0(A_473)))
      | ~ l1_orders_2(A_473) ) ),
    inference(resolution,[status(thm)],[c_34,c_320])).

tff(c_6712,plain,(
    ! [A_475] :
      ( k1_yellow_0(A_475,k5_waybel_0(A_475,'#skF_4'(A_475,u1_struct_0(A_475)))) = '#skF_4'(A_475,u1_struct_0(A_475))
      | ~ v5_orders_2(A_475)
      | ~ v4_orders_2(A_475)
      | ~ v3_orders_2(A_475)
      | v2_struct_0(A_475)
      | v13_waybel_0(u1_struct_0(A_475),A_475)
      | ~ l1_orders_2(A_475) ) ),
    inference(resolution,[status(thm)],[c_156,c_6697])).

tff(c_6735,plain,
    ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),'#skF_4'('#skF_5',u1_struct_0('#skF_5')))
    | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_4'('#skF_5',u1_struct_0('#skF_5'))))
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6712,c_312])).

tff(c_6764,plain,
    ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),'#skF_4'('#skF_5',u1_struct_0('#skF_5')))
    | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_4'('#skF_5',u1_struct_0('#skF_5'))))
    | v2_struct_0('#skF_5')
    | v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_62,c_60,c_58,c_6735])).

tff(c_6765,plain,
    ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),'#skF_4'('#skF_5',u1_struct_0('#skF_5')))
    | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_4'('#skF_5',u1_struct_0('#skF_5'))))
    | v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6764])).

tff(c_6771,plain,(
    ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_4'('#skF_5',u1_struct_0('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_6765])).

tff(c_6774,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_5',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_6771])).

tff(c_6777,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_5',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_6774])).

tff(c_6778,plain,(
    ~ m1_subset_1('#skF_4'('#skF_5',u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6777])).

tff(c_6781,plain,
    ( v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5')
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_6778])).

tff(c_6787,plain,(
    v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_156,c_6781])).

tff(c_7082,plain,(
    ! [C_490,B_491] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_490),B_491)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_491)
      | ~ v13_waybel_0(B_491,'#skF_5')
      | ~ m1_subset_1(B_491,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',C_490)
      | ~ r2_hidden(k1_yellow_0('#skF_5',C_490),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_170,c_7043])).

tff(c_7088,plain,(
    ! [C_490] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_490),u1_struct_0('#skF_5'))
      | ~ r2_hidden(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5')
      | ~ r1_yellow_0('#skF_5',C_490)
      | ~ r2_hidden(k1_yellow_0('#skF_5',C_490),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_156,c_7082])).

tff(c_7094,plain,(
    ! [C_490] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_490),u1_struct_0('#skF_5'))
      | ~ r2_hidden(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',C_490)
      | ~ r2_hidden(k1_yellow_0('#skF_5',C_490),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6787,c_7088])).

tff(c_7098,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_7094])).

tff(c_8273,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8239,c_7098])).

tff(c_8294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_8273])).

tff(c_8315,plain,(
    ! [C_604] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_604),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',C_604)
      | ~ r2_hidden(k1_yellow_0('#skF_5',C_604),'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_7094])).

tff(c_8361,plain,(
    ! [A_605] :
      ( r2_hidden(A_605,u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_605))
      | ~ r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_605)),'#skF_6')
      | ~ r2_hidden(A_605,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_8315])).

tff(c_8441,plain,(
    ! [A_607] :
      ( r2_hidden(A_607,u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_607))
      | ~ r2_hidden(A_607,'#skF_6')
      | ~ r2_hidden(A_607,'#skF_6')
      | ~ r2_hidden(A_607,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_8361])).

tff(c_8477,plain,(
    ! [A_609] :
      ( u1_struct_0('#skF_5') = A_609
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_609))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(A_609,u1_struct_0('#skF_5'))))
      | ~ r2_hidden('#skF_1'(A_609,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_8441,c_4])).

tff(c_8480,plain,(
    ! [A_609] :
      ( u1_struct_0('#skF_5') = A_609
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_609))
      | ~ r2_hidden('#skF_1'(A_609,u1_struct_0('#skF_5')),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_609,u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_8477])).

tff(c_8483,plain,(
    ! [A_609] :
      ( u1_struct_0('#skF_5') = A_609
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_609))
      | ~ r2_hidden('#skF_1'(A_609,u1_struct_0('#skF_5')),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_609,u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_8480])).

tff(c_8485,plain,(
    ! [A_610] :
      ( u1_struct_0('#skF_5') = A_610
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_610))
      | ~ r2_hidden('#skF_1'(A_610,u1_struct_0('#skF_5')),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_610,u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_8483])).

tff(c_8498,plain,(
    ! [A_611] :
      ( u1_struct_0('#skF_5') = A_611
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_611))
      | ~ r2_hidden('#skF_1'(A_611,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_170,c_8485])).

tff(c_8501,plain,(
    ! [A_611] :
      ( u1_struct_0('#skF_5') = A_611
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_611))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1('#skF_1'(A_611,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_12,c_8498])).

tff(c_8543,plain,(
    ! [A_616] :
      ( u1_struct_0('#skF_5') = A_616
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_616))
      | ~ m1_subset_1('#skF_1'(A_616,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_8501])).

tff(c_8548,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6,c_8543])).

tff(c_8549,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_8548])).

tff(c_11851,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11787,c_8549])).

tff(c_11880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_11851])).

tff(c_11881,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_8548])).

tff(c_11939,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11881,c_245])).

tff(c_11947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_11939])).

tff(c_11948,plain,
    ( v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5')
    | r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),'#skF_4'('#skF_5',u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_6765])).

tff(c_11950,plain,(
    r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),'#skF_4'('#skF_5',u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_11948])).

tff(c_11955,plain,(
    ! [B_34] :
      ( r2_hidden('#skF_4'('#skF_5',u1_struct_0('#skF_5')),B_34)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_34)
      | ~ m1_subset_1('#skF_4'('#skF_5',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_34,'#skF_5')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_11950,c_26])).

tff(c_11958,plain,(
    ! [B_34] :
      ( r2_hidden('#skF_4'('#skF_5',u1_struct_0('#skF_5')),B_34)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_34)
      | ~ m1_subset_1('#skF_4'('#skF_5',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_34,'#skF_5')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_11955])).

tff(c_12049,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_11958])).

tff(c_12052,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_170,c_12049])).

tff(c_12059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_12052])).

tff(c_12061,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_11958])).

tff(c_20,plain,(
    ! [A_14,B_17,C_18] :
      ( r1_orders_2(A_14,k1_yellow_0(A_14,B_17),k1_yellow_0(A_14,C_18))
      | ~ r1_yellow_0(A_14,C_18)
      | ~ r1_yellow_0(A_14,B_17)
      | ~ r1_tarski(B_17,C_18)
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_23559,plain,(
    ! [A_1424,C_1425,B_1426,B_1427] :
      ( r2_hidden(k1_yellow_0(A_1424,C_1425),B_1426)
      | ~ r2_hidden(k1_yellow_0(A_1424,B_1427),B_1426)
      | ~ m1_subset_1(k1_yellow_0(A_1424,C_1425),u1_struct_0(A_1424))
      | ~ m1_subset_1(k1_yellow_0(A_1424,B_1427),u1_struct_0(A_1424))
      | ~ v13_waybel_0(B_1426,A_1424)
      | ~ m1_subset_1(B_1426,k1_zfmisc_1(u1_struct_0(A_1424)))
      | ~ r1_yellow_0(A_1424,C_1425)
      | ~ r1_yellow_0(A_1424,B_1427)
      | ~ r1_tarski(B_1427,C_1425)
      | ~ l1_orders_2(A_1424) ) ),
    inference(resolution,[status(thm)],[c_20,c_450])).

tff(c_23578,plain,(
    ! [C_1425,B_1426] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_1425),B_1426)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1426)
      | ~ m1_subset_1(k1_yellow_0('#skF_5',C_1425),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k1_yellow_0('#skF_5',k1_xboole_0),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1426,'#skF_5')
      | ~ m1_subset_1(B_1426,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',C_1425)
      | ~ r1_yellow_0('#skF_5',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,C_1425)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_23559])).

tff(c_23592,plain,(
    ! [C_1429,B_1430] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_1429),B_1430)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1430)
      | ~ m1_subset_1(k1_yellow_0('#skF_5',C_1429),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1430,'#skF_5')
      | ~ m1_subset_1(B_1430,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',C_1429) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2,c_313,c_12061,c_81,c_23578])).

tff(c_23599,plain,(
    ! [B_3,B_1430] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3))),B_1430)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1430)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1430,'#skF_5')
      | ~ m1_subset_1(B_1430,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_23592])).

tff(c_23621,plain,(
    ! [B_3,B_1430] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3))),B_1430)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1430)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1430,'#skF_5')
      | ~ m1_subset_1(B_1430,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_23599])).

tff(c_25872,plain,(
    ! [B_1599,B_1600] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_1599))),B_1600)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1600)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1599),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1600,'#skF_5')
      | ~ m1_subset_1(B_1600,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_1599)))
      | u1_struct_0('#skF_5') = B_1599
      | ~ m1_subset_1(B_1599,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_23621])).

tff(c_25899,plain,(
    ! [B_3,B_1600] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_3),B_1600)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1600)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1600,'#skF_5')
      | ~ m1_subset_1(B_1600,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_25872])).

tff(c_25916,plain,(
    ! [B_3,B_1600] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_3),B_1600)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1600)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1600,'#skF_5')
      | ~ m1_subset_1(B_1600,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_25899])).

tff(c_25918,plain,(
    ! [B_1601,B_1602] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1601),B_1602)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1602)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1601),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1602,'#skF_5')
      | ~ m1_subset_1(B_1602,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_1601)))
      | u1_struct_0('#skF_5') = B_1601
      | ~ m1_subset_1(B_1601,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_25916])).

tff(c_25921,plain,(
    ! [B_1601,B_1602] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1601),B_1602)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1602)
      | ~ v13_waybel_0(B_1602,'#skF_5')
      | ~ m1_subset_1(B_1602,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_1601
      | ~ m1_subset_1(B_1601,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1601),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_25918])).

tff(c_25924,plain,(
    ! [B_1601,B_1602] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1601),B_1602)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1602)
      | ~ v13_waybel_0(B_1602,'#skF_5')
      | ~ m1_subset_1(B_1602,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_1601
      | ~ m1_subset_1(B_1601,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1601),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_25921])).

tff(c_25926,plain,(
    ! [B_1603,B_1604] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1603),B_1604)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1604)
      | ~ v13_waybel_0(B_1604,'#skF_5')
      | ~ m1_subset_1(B_1604,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_1603
      | ~ m1_subset_1(B_1603,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1603),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_25924])).

tff(c_25935,plain,(
    ! [B_1605,B_1606] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1605),B_1606)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1606)
      | ~ v13_waybel_0(B_1606,'#skF_5')
      | ~ m1_subset_1(B_1606,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_1605
      | ~ m1_subset_1(B_1605,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_25926])).

tff(c_25965,plain,(
    ! [B_1607] :
      ( ~ r2_hidden(k3_yellow_0('#skF_5'),B_1607)
      | ~ v13_waybel_0(B_1607,'#skF_5')
      | u1_struct_0('#skF_5') = B_1607
      | ~ m1_subset_1(B_1607,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_25935,c_4])).

tff(c_25976,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v13_waybel_0('#skF_6','#skF_5')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_25965])).

tff(c_25981,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_140,c_25976])).

tff(c_17227,plain,(
    ! [A_1069,C_1070,B_1071,B_1072] :
      ( r2_hidden(k1_yellow_0(A_1069,C_1070),B_1071)
      | ~ r2_hidden(k1_yellow_0(A_1069,B_1072),B_1071)
      | ~ m1_subset_1(k1_yellow_0(A_1069,C_1070),u1_struct_0(A_1069))
      | ~ m1_subset_1(k1_yellow_0(A_1069,B_1072),u1_struct_0(A_1069))
      | ~ v13_waybel_0(B_1071,A_1069)
      | ~ m1_subset_1(B_1071,k1_zfmisc_1(u1_struct_0(A_1069)))
      | ~ r1_yellow_0(A_1069,C_1070)
      | ~ r1_yellow_0(A_1069,B_1072)
      | ~ r1_tarski(B_1072,C_1070)
      | ~ l1_orders_2(A_1069) ) ),
    inference(resolution,[status(thm)],[c_20,c_450])).

tff(c_17246,plain,(
    ! [C_1070,B_1071] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_1070),B_1071)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1071)
      | ~ m1_subset_1(k1_yellow_0('#skF_5',C_1070),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k1_yellow_0('#skF_5',k1_xboole_0),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1071,'#skF_5')
      | ~ m1_subset_1(B_1071,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',C_1070)
      | ~ r1_yellow_0('#skF_5',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,C_1070)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_17227])).

tff(c_17256,plain,(
    ! [C_1073,B_1074] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_1073),B_1074)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1074)
      | ~ m1_subset_1(k1_yellow_0('#skF_5',C_1073),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1074,'#skF_5')
      | ~ m1_subset_1(B_1074,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',C_1073) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2,c_313,c_12061,c_81,c_17246])).

tff(c_17263,plain,(
    ! [B_3,B_1074] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3))),B_1074)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1074)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1074,'#skF_5')
      | ~ m1_subset_1(B_1074,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_17256])).

tff(c_17285,plain,(
    ! [B_3,B_1074] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3))),B_1074)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1074)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1074,'#skF_5')
      | ~ m1_subset_1(B_1074,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_17263])).

tff(c_23045,plain,(
    ! [B_1404,B_1405] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_1404))),B_1405)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1405)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1404),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1405,'#skF_5')
      | ~ m1_subset_1(B_1405,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_1404)))
      | u1_struct_0('#skF_5') = B_1404
      | ~ m1_subset_1(B_1404,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_17285])).

tff(c_23082,plain,(
    ! [B_3,B_1405] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_3),B_1405)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1405)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1405,'#skF_5')
      | ~ m1_subset_1(B_1405,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_23045])).

tff(c_23106,plain,(
    ! [B_3,B_1405] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_3),B_1405)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1405)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1405,'#skF_5')
      | ~ m1_subset_1(B_1405,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_23082])).

tff(c_23108,plain,(
    ! [B_1406,B_1407] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1406),B_1407)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1407)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1406),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1407,'#skF_5')
      | ~ m1_subset_1(B_1407,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_1406)))
      | u1_struct_0('#skF_5') = B_1406
      | ~ m1_subset_1(B_1406,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_23106])).

tff(c_23111,plain,(
    ! [B_1406,B_1407] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1406),B_1407)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1407)
      | ~ v13_waybel_0(B_1407,'#skF_5')
      | ~ m1_subset_1(B_1407,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_1406
      | ~ m1_subset_1(B_1406,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1406),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_23108])).

tff(c_23114,plain,(
    ! [B_1406,B_1407] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1406),B_1407)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1407)
      | ~ v13_waybel_0(B_1407,'#skF_5')
      | ~ m1_subset_1(B_1407,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_1406
      | ~ m1_subset_1(B_1406,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1406),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_23111])).

tff(c_23116,plain,(
    ! [B_1408,B_1409] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1408),B_1409)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1409)
      | ~ v13_waybel_0(B_1409,'#skF_5')
      | ~ m1_subset_1(B_1409,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_1408
      | ~ m1_subset_1(B_1408,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1408),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_23114])).

tff(c_23125,plain,(
    ! [B_1410,B_1411] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1410),B_1411)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1411)
      | ~ v13_waybel_0(B_1411,'#skF_5')
      | ~ m1_subset_1(B_1411,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_1410
      | ~ m1_subset_1(B_1410,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_23116])).

tff(c_23166,plain,(
    ! [B_1412] :
      ( ~ r2_hidden(k3_yellow_0('#skF_5'),B_1412)
      | ~ v13_waybel_0(B_1412,'#skF_5')
      | u1_struct_0('#skF_5') = B_1412
      | ~ m1_subset_1(B_1412,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_23125,c_4])).

tff(c_23177,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v13_waybel_0('#skF_6','#skF_5')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_23166])).

tff(c_23185,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_140,c_23177])).

tff(c_18916,plain,(
    ! [B_1208,B_1209] :
      ( r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_1208))),B_1209)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1209)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1208),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1209,'#skF_5')
      | ~ m1_subset_1(B_1209,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_1208)))
      | u1_struct_0('#skF_5') = B_1208
      | ~ m1_subset_1(B_1208,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_17285])).

tff(c_18943,plain,(
    ! [B_3,B_1209] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_3),B_1209)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1209)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1209,'#skF_5')
      | ~ m1_subset_1(B_1209,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_18916])).

tff(c_18960,plain,(
    ! [B_3,B_1209] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_3),B_1209)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1209)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_3),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1209,'#skF_5')
      | ~ m1_subset_1(B_1209,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_3)))
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_18943])).

tff(c_18962,plain,(
    ! [B_1210,B_1211] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1210),B_1211)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1211)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1210),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1211,'#skF_5')
      | ~ m1_subset_1(B_1211,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(u1_struct_0('#skF_5'),B_1210)))
      | u1_struct_0('#skF_5') = B_1210
      | ~ m1_subset_1(B_1210,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_18960])).

tff(c_18965,plain,(
    ! [B_1210,B_1211] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1210),B_1211)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1211)
      | ~ v13_waybel_0(B_1211,'#skF_5')
      | ~ m1_subset_1(B_1211,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_1210
      | ~ m1_subset_1(B_1210,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1210),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_18962])).

tff(c_18968,plain,(
    ! [B_1210,B_1211] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1210),B_1211)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1211)
      | ~ v13_waybel_0(B_1211,'#skF_5')
      | ~ m1_subset_1(B_1211,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_1210
      | ~ m1_subset_1(B_1210,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1210),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_18965])).

tff(c_18970,plain,(
    ! [B_1212,B_1213] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1212),B_1213)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1213)
      | ~ v13_waybel_0(B_1213,'#skF_5')
      | ~ m1_subset_1(B_1213,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_1212
      | ~ m1_subset_1(B_1212,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_1212),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_18968])).

tff(c_18979,plain,(
    ! [B_1214,B_1215] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1214),B_1215)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1215)
      | ~ v13_waybel_0(B_1215,'#skF_5')
      | ~ m1_subset_1(B_1215,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_1214
      | ~ m1_subset_1(B_1214,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_18970])).

tff(c_19003,plain,(
    ! [B_1216] :
      ( ~ r2_hidden(k3_yellow_0('#skF_5'),B_1216)
      | ~ v13_waybel_0(B_1216,'#skF_5')
      | u1_struct_0('#skF_5') = B_1216
      | ~ m1_subset_1(B_1216,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_18979,c_4])).

tff(c_19014,plain,
    ( ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v13_waybel_0('#skF_6','#skF_5')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_19003])).

tff(c_19021,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_140,c_19014])).

tff(c_11949,plain,(
    r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_4'('#skF_5',u1_struct_0('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_6765])).

tff(c_343,plain,(
    ! [A_112] :
      ( k1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_112)) = A_112
      | ~ r2_hidden(A_112,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_340])).

tff(c_352,plain,(
    ! [A_112,C_18] :
      ( r1_orders_2('#skF_5',A_112,k1_yellow_0('#skF_5',C_18))
      | ~ r1_yellow_0('#skF_5',C_18)
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_112))
      | ~ r1_tarski(k5_waybel_0('#skF_5',A_112),C_18)
      | ~ l1_orders_2('#skF_5')
      | ~ r2_hidden(A_112,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_20])).

tff(c_361,plain,(
    ! [A_112,C_18] :
      ( r1_orders_2('#skF_5',A_112,k1_yellow_0('#skF_5',C_18))
      | ~ r1_yellow_0('#skF_5',C_18)
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_112))
      | ~ r1_tarski(k5_waybel_0('#skF_5',A_112),C_18)
      | ~ r2_hidden(A_112,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_352])).

tff(c_6723,plain,(
    ! [A_112] :
      ( r1_orders_2('#skF_5',A_112,'#skF_4'('#skF_5',u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_4'('#skF_5',u1_struct_0('#skF_5'))))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_112))
      | ~ r1_tarski(k5_waybel_0('#skF_5',A_112),k5_waybel_0('#skF_5','#skF_4'('#skF_5',u1_struct_0('#skF_5'))))
      | ~ r2_hidden(A_112,'#skF_6')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6712,c_361])).

tff(c_6754,plain,(
    ! [A_112] :
      ( r1_orders_2('#skF_5',A_112,'#skF_4'('#skF_5',u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_4'('#skF_5',u1_struct_0('#skF_5'))))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_112))
      | ~ r1_tarski(k5_waybel_0('#skF_5',A_112),k5_waybel_0('#skF_5','#skF_4'('#skF_5',u1_struct_0('#skF_5'))))
      | ~ r2_hidden(A_112,'#skF_6')
      | v2_struct_0('#skF_5')
      | v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_62,c_60,c_58,c_6723])).

tff(c_6755,plain,(
    ! [A_112] :
      ( r1_orders_2('#skF_5',A_112,'#skF_4'('#skF_5',u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_4'('#skF_5',u1_struct_0('#skF_5'))))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_112))
      | ~ r1_tarski(k5_waybel_0('#skF_5',A_112),k5_waybel_0('#skF_5','#skF_4'('#skF_5',u1_struct_0('#skF_5'))))
      | ~ r2_hidden(A_112,'#skF_6')
      | v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6754])).

tff(c_17071,plain,(
    ! [A_112] :
      ( r1_orders_2('#skF_5',A_112,'#skF_4'('#skF_5',u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_112))
      | ~ r1_tarski(k5_waybel_0('#skF_5',A_112),k5_waybel_0('#skF_5','#skF_4'('#skF_5',u1_struct_0('#skF_5'))))
      | ~ r2_hidden(A_112,'#skF_6')
      | v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11949,c_6755])).

tff(c_17072,plain,(
    v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_17071])).

tff(c_17299,plain,(
    ! [C_1075,B_1076] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_1075),B_1076)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1076)
      | ~ v13_waybel_0(B_1076,'#skF_5')
      | ~ m1_subset_1(B_1076,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',C_1075)
      | ~ r2_hidden(k1_yellow_0('#skF_5',C_1075),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_170,c_17256])).

tff(c_17305,plain,(
    ! [C_1075] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_1075),u1_struct_0('#skF_5'))
      | ~ r2_hidden(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5')
      | ~ r1_yellow_0('#skF_5',C_1075)
      | ~ r2_hidden(k1_yellow_0('#skF_5',C_1075),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_156,c_17299])).

tff(c_17311,plain,(
    ! [C_1075] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_1075),u1_struct_0('#skF_5'))
      | ~ r2_hidden(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',C_1075)
      | ~ r2_hidden(k1_yellow_0('#skF_5',C_1075),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17072,c_17305])).

tff(c_17315,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_17311])).

tff(c_19076,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19021,c_17315])).

tff(c_19108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_19076])).

tff(c_19120,plain,(
    ! [C_1219] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_1219),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',C_1219)
      | ~ r2_hidden(k1_yellow_0('#skF_5',C_1219),'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_17311])).

tff(c_19221,plain,(
    ! [A_1221] :
      ( r2_hidden(A_1221,u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_1221))
      | ~ r2_hidden(k1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_1221)),'#skF_6')
      | ~ r2_hidden(A_1221,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_19120])).

tff(c_19269,plain,(
    ! [A_1222] :
      ( r2_hidden(A_1222,u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5',A_1222))
      | ~ r2_hidden(A_1222,'#skF_6')
      | ~ r2_hidden(A_1222,'#skF_6')
      | ~ r2_hidden(A_1222,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_19221])).

tff(c_19395,plain,(
    ! [A_1227] :
      ( u1_struct_0('#skF_5') = A_1227
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_1227))
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5','#skF_1'(A_1227,u1_struct_0('#skF_5'))))
      | ~ r2_hidden('#skF_1'(A_1227,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_19269,c_4])).

tff(c_19398,plain,(
    ! [A_1227] :
      ( u1_struct_0('#skF_5') = A_1227
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_1227))
      | ~ r2_hidden('#skF_1'(A_1227,u1_struct_0('#skF_5')),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_1227,u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_19395])).

tff(c_19401,plain,(
    ! [A_1227] :
      ( u1_struct_0('#skF_5') = A_1227
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_1227))
      | ~ r2_hidden('#skF_1'(A_1227,u1_struct_0('#skF_5')),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_1227,u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_19398])).

tff(c_19403,plain,(
    ! [A_1228] :
      ( u1_struct_0('#skF_5') = A_1228
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_1228))
      | ~ r2_hidden('#skF_1'(A_1228,u1_struct_0('#skF_5')),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_1228,u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_19401])).

tff(c_19416,plain,(
    ! [A_1229] :
      ( u1_struct_0('#skF_5') = A_1229
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_1229))
      | ~ r2_hidden('#skF_1'(A_1229,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_170,c_19403])).

tff(c_19419,plain,(
    ! [A_1229] :
      ( u1_struct_0('#skF_5') = A_1229
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_1229))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1('#skF_1'(A_1229,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_12,c_19416])).

tff(c_19423,plain,(
    ! [A_1230] :
      ( u1_struct_0('#skF_5') = A_1230
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_1230))
      | ~ m1_subset_1('#skF_1'(A_1230,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_19419])).

tff(c_19428,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6,c_19423])).

tff(c_19429,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_19428])).

tff(c_23265,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23185,c_19429])).

tff(c_23307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_23265])).

tff(c_23308,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_19428])).

tff(c_23385,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23308,c_245])).

tff(c_23393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_23385])).

tff(c_23395,plain,(
    ~ v13_waybel_0(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_17071])).

tff(c_26070,plain,(
    ~ v13_waybel_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25981,c_23395])).

tff(c_26091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_26070])).

tff(c_26099,plain,(
    ! [A_1610] :
      ( u1_struct_0('#skF_5') = A_1610
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_1610))
      | ~ r2_hidden('#skF_1'(A_1610,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_26102,plain,(
    ! [A_1610] :
      ( u1_struct_0('#skF_5') = A_1610
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_1610))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1('#skF_1'(A_1610,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_12,c_26099])).

tff(c_26106,plain,(
    ! [A_1611] :
      ( u1_struct_0('#skF_5') = A_1611
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_1611))
      | ~ m1_subset_1('#skF_1'(A_1611,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_26102])).

tff(c_26111,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6,c_26106])).

tff(c_26112,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_26111])).

tff(c_29825,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29750,c_26112])).

tff(c_29837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_29825])).

tff(c_29838,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_26111])).

tff(c_141,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_29845,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29838,c_141])).

tff(c_29848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_29845])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.06/9.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.24/9.99  
% 19.24/9.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.24/10.00  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 19.24/10.00  
% 19.24/10.00  %Foreground sorts:
% 19.24/10.00  
% 19.24/10.00  
% 19.24/10.00  %Background operators:
% 19.24/10.00  
% 19.24/10.00  
% 19.24/10.00  %Foreground operators:
% 19.24/10.00  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 19.24/10.00  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 19.24/10.00  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 19.24/10.00  tff('#skF_2', type, '#skF_2': $i > $i).
% 19.24/10.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.24/10.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.24/10.00  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 19.24/10.00  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 19.24/10.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.24/10.00  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 19.24/10.00  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 19.24/10.00  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 19.24/10.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.24/10.00  tff('#skF_5', type, '#skF_5': $i).
% 19.24/10.00  tff('#skF_6', type, '#skF_6': $i).
% 19.24/10.00  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 19.24/10.00  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 19.24/10.00  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 19.24/10.00  tff(k5_waybel_0, type, k5_waybel_0: ($i * $i) > $i).
% 19.24/10.00  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 19.24/10.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.24/10.00  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 19.24/10.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.24/10.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.24/10.00  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 19.24/10.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 19.24/10.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 19.24/10.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 19.24/10.00  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 19.24/10.00  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 19.24/10.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.24/10.00  
% 19.24/10.04  tff(f_42, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 19.24/10.04  tff(f_130, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 19.24/10.04  tff(f_159, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 19.24/10.04  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 19.24/10.04  tff(f_62, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 19.24/10.04  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 19.24/10.04  tff(f_123, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r1_yellow_0(A, k5_waybel_0(A, B)) & (k1_yellow_0(A, k5_waybel_0(A, B)) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_waybel_0)).
% 19.24/10.04  tff(f_54, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 19.24/10.04  tff(f_86, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 19.24/10.04  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 19.24/10.04  tff(f_58, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 19.24/10.04  tff(f_73, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (((r1_tarski(B, C) & r1_yellow_0(A, B)) & r1_yellow_0(A, C)) => r1_orders_2(A, k1_yellow_0(A, B), k1_yellow_0(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_yellow_0)).
% 19.24/10.04  tff(f_105, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 19.24/10.04  tff(c_8, plain, (![A_5]: (~v1_subset_1('#skF_2'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 19.24/10.04  tff(c_10, plain, (![A_5]: (m1_subset_1('#skF_2'(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 19.24/10.04  tff(c_144, plain, (![B_66, A_67]: (v1_subset_1(B_66, A_67) | B_66=A_67 | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_130])).
% 19.24/10.04  tff(c_150, plain, (![A_5]: (v1_subset_1('#skF_2'(A_5), A_5) | '#skF_2'(A_5)=A_5)), inference(resolution, [status(thm)], [c_10, c_144])).
% 19.24/10.04  tff(c_155, plain, (![A_5]: ('#skF_2'(A_5)=A_5)), inference(negUnitSimplification, [status(thm)], [c_8, c_150])).
% 19.24/10.04  tff(c_157, plain, (![A_5]: (~v1_subset_1(A_5, A_5))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_8])).
% 19.24/10.04  tff(c_156, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_10])).
% 19.24/10.04  tff(c_48, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 19.24/10.04  tff(c_66, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 19.24/10.04  tff(c_88, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_66])).
% 19.24/10.04  tff(c_52, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_159])).
% 19.24/10.04  tff(c_12, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 19.24/10.04  tff(c_72, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_159])).
% 19.24/10.04  tff(c_89, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_72])).
% 19.24/10.04  tff(c_92, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_12, c_89])).
% 19.24/10.04  tff(c_95, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_52, c_92])).
% 19.24/10.04  tff(c_54, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 19.24/10.04  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 19.24/10.04  tff(c_96, plain, (![B_59, A_60]: (v1_subset_1(B_59, A_60) | B_59=A_60 | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_130])).
% 19.24/10.04  tff(c_99, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_46, c_96])).
% 19.24/10.04  tff(c_105, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_88, c_99])).
% 19.24/10.04  tff(c_18, plain, (![A_13]: (m1_subset_1(k3_yellow_0(A_13), u1_struct_0(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 19.24/10.04  tff(c_130, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6') | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_105, c_18])).
% 19.24/10.04  tff(c_134, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_130])).
% 19.24/10.04  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_134])).
% 19.24/10.04  tff(c_137, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_72])).
% 19.24/10.04  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_137])).
% 19.24/10.04  tff(c_140, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_66])).
% 19.24/10.04  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1('#skF_1'(A_2, B_3), A_2) | B_3=A_2 | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 19.24/10.04  tff(c_64, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 19.24/10.04  tff(c_62, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 19.24/10.04  tff(c_60, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 19.24/10.04  tff(c_58, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 19.24/10.04  tff(c_40, plain, (![A_45, B_47]: (r1_yellow_0(A_45, k5_waybel_0(A_45, B_47)) | ~m1_subset_1(B_47, u1_struct_0(A_45)) | ~l1_orders_2(A_45) | ~v5_orders_2(A_45) | ~v4_orders_2(A_45) | ~v3_orders_2(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_123])).
% 19.24/10.04  tff(c_26184, plain, (![A_1630, B_1631]: (k1_yellow_0(A_1630, k5_waybel_0(A_1630, B_1631))=B_1631 | ~m1_subset_1(B_1631, u1_struct_0(A_1630)) | ~l1_orders_2(A_1630) | ~v5_orders_2(A_1630) | ~v4_orders_2(A_1630) | ~v3_orders_2(A_1630) | v2_struct_0(A_1630))), inference(cnfTransformation, [status(thm)], [f_123])).
% 19.24/10.04  tff(c_26201, plain, (![A_1630, B_3]: (k1_yellow_0(A_1630, k5_waybel_0(A_1630, '#skF_1'(u1_struct_0(A_1630), B_3)))='#skF_1'(u1_struct_0(A_1630), B_3) | ~l1_orders_2(A_1630) | ~v5_orders_2(A_1630) | ~v4_orders_2(A_1630) | ~v3_orders_2(A_1630) | v2_struct_0(A_1630) | u1_struct_0(A_1630)=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0(A_1630))))), inference(resolution, [status(thm)], [c_6, c_26184])).
% 19.24/10.04  tff(c_167, plain, (![A_69, C_70, B_71]: (m1_subset_1(A_69, C_70) | ~m1_subset_1(B_71, k1_zfmisc_1(C_70)) | ~r2_hidden(A_69, B_71))), inference(cnfTransformation, [status(thm)], [f_54])).
% 19.24/10.04  tff(c_170, plain, (![A_69]: (m1_subset_1(A_69, u1_struct_0('#skF_5')) | ~r2_hidden(A_69, '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_167])).
% 19.24/10.04  tff(c_56, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 19.24/10.04  tff(c_24, plain, (![A_19]: (r1_yellow_0(A_19, k1_xboole_0) | ~l1_orders_2(A_19) | ~v1_yellow_0(A_19) | ~v5_orders_2(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_86])).
% 19.24/10.04  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.24/10.04  tff(c_77, plain, (![A_55]: (k1_yellow_0(A_55, k1_xboole_0)=k3_yellow_0(A_55) | ~l1_orders_2(A_55))), inference(cnfTransformation, [status(thm)], [f_58])).
% 19.24/10.04  tff(c_81, plain, (k1_yellow_0('#skF_5', k1_xboole_0)=k3_yellow_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_77])).
% 19.24/10.04  tff(c_26162, plain, (![A_1627, B_1628, C_1629]: (r1_orders_2(A_1627, k1_yellow_0(A_1627, B_1628), k1_yellow_0(A_1627, C_1629)) | ~r1_yellow_0(A_1627, C_1629) | ~r1_yellow_0(A_1627, B_1628) | ~r1_tarski(B_1628, C_1629) | ~l1_orders_2(A_1627))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.24/10.04  tff(c_26165, plain, (![C_1629]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), k1_yellow_0('#skF_5', C_1629)) | ~r1_yellow_0('#skF_5', C_1629) | ~r1_yellow_0('#skF_5', k1_xboole_0) | ~r1_tarski(k1_xboole_0, C_1629) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_26162])).
% 19.24/10.04  tff(c_26170, plain, (![C_1629]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), k1_yellow_0('#skF_5', C_1629)) | ~r1_yellow_0('#skF_5', C_1629) | ~r1_yellow_0('#skF_5', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2, c_26165])).
% 19.24/10.04  tff(c_26173, plain, (~r1_yellow_0('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_26170])).
% 19.24/10.04  tff(c_26176, plain, (~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_24, c_26173])).
% 19.24/10.04  tff(c_26179, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_26176])).
% 19.24/10.04  tff(c_26181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_26179])).
% 19.24/10.04  tff(c_26182, plain, (![C_1629]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), k1_yellow_0('#skF_5', C_1629)) | ~r1_yellow_0('#skF_5', C_1629))), inference(splitRight, [status(thm)], [c_26170])).
% 19.24/10.04  tff(c_26294, plain, (![D_1640, B_1641, A_1642, C_1643]: (r2_hidden(D_1640, B_1641) | ~r1_orders_2(A_1642, C_1643, D_1640) | ~r2_hidden(C_1643, B_1641) | ~m1_subset_1(D_1640, u1_struct_0(A_1642)) | ~m1_subset_1(C_1643, u1_struct_0(A_1642)) | ~v13_waybel_0(B_1641, A_1642) | ~m1_subset_1(B_1641, k1_zfmisc_1(u1_struct_0(A_1642))) | ~l1_orders_2(A_1642))), inference(cnfTransformation, [status(thm)], [f_105])).
% 19.24/10.04  tff(c_26304, plain, (![C_1629, B_1641]: (r2_hidden(k1_yellow_0('#skF_5', C_1629), B_1641) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1641) | ~m1_subset_1(k1_yellow_0('#skF_5', C_1629), u1_struct_0('#skF_5')) | ~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1641, '#skF_5') | ~m1_subset_1(B_1641, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~r1_yellow_0('#skF_5', C_1629))), inference(resolution, [status(thm)], [c_26182, c_26294])).
% 19.24/10.04  tff(c_26323, plain, (![C_1629, B_1641]: (r2_hidden(k1_yellow_0('#skF_5', C_1629), B_1641) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1641) | ~m1_subset_1(k1_yellow_0('#skF_5', C_1629), u1_struct_0('#skF_5')) | ~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1641, '#skF_5') | ~m1_subset_1(B_1641, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', C_1629))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_26304])).
% 19.24/10.04  tff(c_26642, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_26323])).
% 19.24/10.04  tff(c_26645, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_170, c_26642])).
% 19.24/10.04  tff(c_26652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_26645])).
% 19.24/10.04  tff(c_26777, plain, (![C_1666, B_1667]: (r2_hidden(k1_yellow_0('#skF_5', C_1666), B_1667) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1667) | ~m1_subset_1(k1_yellow_0('#skF_5', C_1666), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1667, '#skF_5') | ~m1_subset_1(B_1667, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', C_1666))), inference(splitRight, [status(thm)], [c_26323])).
% 19.24/10.04  tff(c_26782, plain, (![B_3, B_1667]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))), B_1667) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1667) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1667, '#skF_5') | ~m1_subset_1(B_1667, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_26201, c_26777])).
% 19.24/10.04  tff(c_26802, plain, (![B_3, B_1667]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))), B_1667) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1667) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1667, '#skF_5') | ~m1_subset_1(B_1667, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_26782])).
% 19.24/10.04  tff(c_29628, plain, (![B_1811, B_1812]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_1811))), B_1812) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1812) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1811), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1812, '#skF_5') | ~m1_subset_1(B_1812, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_1811))) | u1_struct_0('#skF_5')=B_1811 | ~m1_subset_1(B_1811, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_26802])).
% 19.24/10.04  tff(c_29659, plain, (![B_3, B_1812]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_3), B_1812) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1812) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1812, '#skF_5') | ~m1_subset_1(B_1812, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_26201, c_29628])).
% 19.24/10.04  tff(c_29680, plain, (![B_3, B_1812]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_3), B_1812) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1812) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1812, '#skF_5') | ~m1_subset_1(B_1812, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_29659])).
% 19.24/10.04  tff(c_29682, plain, (![B_1813, B_1814]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1813), B_1814) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1814) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1813), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1814, '#skF_5') | ~m1_subset_1(B_1814, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_1813))) | u1_struct_0('#skF_5')=B_1813 | ~m1_subset_1(B_1813, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_29680])).
% 19.24/10.04  tff(c_29685, plain, (![B_1813, B_1814]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1813), B_1814) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1814) | ~v13_waybel_0(B_1814, '#skF_5') | ~m1_subset_1(B_1814, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_1813 | ~m1_subset_1(B_1813, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1813), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_29682])).
% 19.24/10.04  tff(c_29688, plain, (![B_1813, B_1814]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1813), B_1814) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1814) | ~v13_waybel_0(B_1814, '#skF_5') | ~m1_subset_1(B_1814, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_1813 | ~m1_subset_1(B_1813, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1813), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_29685])).
% 19.24/10.04  tff(c_29690, plain, (![B_1815, B_1816]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1815), B_1816) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1816) | ~v13_waybel_0(B_1816, '#skF_5') | ~m1_subset_1(B_1816, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_1815 | ~m1_subset_1(B_1815, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1815), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_29688])).
% 19.24/10.04  tff(c_29699, plain, (![B_1817, B_1818]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1817), B_1818) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1818) | ~v13_waybel_0(B_1818, '#skF_5') | ~m1_subset_1(B_1818, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_1817 | ~m1_subset_1(B_1817, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_6, c_29690])).
% 19.24/10.04  tff(c_4, plain, (![A_2, B_3]: (~r2_hidden('#skF_1'(A_2, B_3), B_3) | B_3=A_2 | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 19.24/10.04  tff(c_29731, plain, (![B_1819]: (~r2_hidden(k3_yellow_0('#skF_5'), B_1819) | ~v13_waybel_0(B_1819, '#skF_5') | u1_struct_0('#skF_5')=B_1819 | ~m1_subset_1(B_1819, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_29699, c_4])).
% 19.24/10.04  tff(c_29742, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_46, c_29731])).
% 19.24/10.04  tff(c_29750, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_140, c_29742])).
% 19.24/10.04  tff(c_320, plain, (![A_110, B_111]: (k1_yellow_0(A_110, k5_waybel_0(A_110, B_111))=B_111 | ~m1_subset_1(B_111, u1_struct_0(A_110)) | ~l1_orders_2(A_110) | ~v5_orders_2(A_110) | ~v4_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_123])).
% 19.24/10.04  tff(c_337, plain, (![A_110, B_3]: (k1_yellow_0(A_110, k5_waybel_0(A_110, '#skF_1'(u1_struct_0(A_110), B_3)))='#skF_1'(u1_struct_0(A_110), B_3) | ~l1_orders_2(A_110) | ~v5_orders_2(A_110) | ~v4_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110) | u1_struct_0(A_110)=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0(A_110))))), inference(resolution, [status(thm)], [c_6, c_320])).
% 19.24/10.04  tff(c_292, plain, (![A_106, B_107, C_108]: (r1_orders_2(A_106, k1_yellow_0(A_106, B_107), k1_yellow_0(A_106, C_108)) | ~r1_yellow_0(A_106, C_108) | ~r1_yellow_0(A_106, B_107) | ~r1_tarski(B_107, C_108) | ~l1_orders_2(A_106))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.24/10.04  tff(c_295, plain, (![C_108]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), k1_yellow_0('#skF_5', C_108)) | ~r1_yellow_0('#skF_5', C_108) | ~r1_yellow_0('#skF_5', k1_xboole_0) | ~r1_tarski(k1_xboole_0, C_108) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_292])).
% 19.24/10.04  tff(c_300, plain, (![C_108]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), k1_yellow_0('#skF_5', C_108)) | ~r1_yellow_0('#skF_5', C_108) | ~r1_yellow_0('#skF_5', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2, c_295])).
% 19.24/10.04  tff(c_303, plain, (~r1_yellow_0('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_300])).
% 19.24/10.04  tff(c_306, plain, (~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_24, c_303])).
% 19.24/10.04  tff(c_309, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_306])).
% 19.24/10.04  tff(c_311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_309])).
% 19.24/10.04  tff(c_313, plain, (r1_yellow_0('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_300])).
% 19.24/10.04  tff(c_312, plain, (![C_108]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), k1_yellow_0('#skF_5', C_108)) | ~r1_yellow_0('#skF_5', C_108))), inference(splitRight, [status(thm)], [c_300])).
% 19.24/10.04  tff(c_450, plain, (![D_124, B_125, A_126, C_127]: (r2_hidden(D_124, B_125) | ~r1_orders_2(A_126, C_127, D_124) | ~r2_hidden(C_127, B_125) | ~m1_subset_1(D_124, u1_struct_0(A_126)) | ~m1_subset_1(C_127, u1_struct_0(A_126)) | ~v13_waybel_0(B_125, A_126) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_orders_2(A_126))), inference(cnfTransformation, [status(thm)], [f_105])).
% 19.24/10.04  tff(c_462, plain, (![C_108, B_125]: (r2_hidden(k1_yellow_0('#skF_5', C_108), B_125) | ~r2_hidden(k3_yellow_0('#skF_5'), B_125) | ~m1_subset_1(k1_yellow_0('#skF_5', C_108), u1_struct_0('#skF_5')) | ~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_125, '#skF_5') | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~r1_yellow_0('#skF_5', C_108))), inference(resolution, [status(thm)], [c_312, c_450])).
% 19.24/10.04  tff(c_484, plain, (![C_108, B_125]: (r2_hidden(k1_yellow_0('#skF_5', C_108), B_125) | ~r2_hidden(k3_yellow_0('#skF_5'), B_125) | ~m1_subset_1(k1_yellow_0('#skF_5', C_108), u1_struct_0('#skF_5')) | ~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_125, '#skF_5') | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', C_108))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_462])).
% 19.24/10.04  tff(c_775, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_484])).
% 19.24/10.04  tff(c_784, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_170, c_775])).
% 19.24/10.04  tff(c_791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_784])).
% 19.24/10.04  tff(c_907, plain, (![C_144, B_145]: (r2_hidden(k1_yellow_0('#skF_5', C_144), B_145) | ~r2_hidden(k3_yellow_0('#skF_5'), B_145) | ~m1_subset_1(k1_yellow_0('#skF_5', C_144), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_145, '#skF_5') | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', C_144))), inference(splitRight, [status(thm)], [c_484])).
% 19.24/10.04  tff(c_912, plain, (![B_3, B_145]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))), B_145) | ~r2_hidden(k3_yellow_0('#skF_5'), B_145) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_145, '#skF_5') | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_337, c_907])).
% 19.24/10.04  tff(c_932, plain, (![B_3, B_145]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))), B_145) | ~r2_hidden(k3_yellow_0('#skF_5'), B_145) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_145, '#skF_5') | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_912])).
% 19.24/10.04  tff(c_6405, plain, (![B_461, B_462]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_461))), B_462) | ~r2_hidden(k3_yellow_0('#skF_5'), B_462) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_461), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_462, '#skF_5') | ~m1_subset_1(B_462, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_461))) | u1_struct_0('#skF_5')=B_461 | ~m1_subset_1(B_461, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_932])).
% 19.24/10.04  tff(c_6440, plain, (![B_3, B_462]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_3), B_462) | ~r2_hidden(k3_yellow_0('#skF_5'), B_462) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_462, '#skF_5') | ~m1_subset_1(B_462, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_337, c_6405])).
% 19.24/10.04  tff(c_6463, plain, (![B_3, B_462]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_3), B_462) | ~r2_hidden(k3_yellow_0('#skF_5'), B_462) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_462, '#skF_5') | ~m1_subset_1(B_462, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_6440])).
% 19.24/10.04  tff(c_6465, plain, (![B_463, B_464]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_463), B_464) | ~r2_hidden(k3_yellow_0('#skF_5'), B_464) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_463), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_464, '#skF_5') | ~m1_subset_1(B_464, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_463))) | u1_struct_0('#skF_5')=B_463 | ~m1_subset_1(B_463, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_6463])).
% 19.24/10.04  tff(c_6468, plain, (![B_463, B_464]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_463), B_464) | ~r2_hidden(k3_yellow_0('#skF_5'), B_464) | ~v13_waybel_0(B_464, '#skF_5') | ~m1_subset_1(B_464, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_463 | ~m1_subset_1(B_463, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_463), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_6465])).
% 19.24/10.04  tff(c_6471, plain, (![B_463, B_464]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_463), B_464) | ~r2_hidden(k3_yellow_0('#skF_5'), B_464) | ~v13_waybel_0(B_464, '#skF_5') | ~m1_subset_1(B_464, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_463 | ~m1_subset_1(B_463, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_463), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_6468])).
% 19.24/10.04  tff(c_6473, plain, (![B_465, B_466]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_465), B_466) | ~r2_hidden(k3_yellow_0('#skF_5'), B_466) | ~v13_waybel_0(B_466, '#skF_5') | ~m1_subset_1(B_466, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_465 | ~m1_subset_1(B_465, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_465), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_6471])).
% 19.24/10.04  tff(c_6482, plain, (![B_467, B_468]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_467), B_468) | ~r2_hidden(k3_yellow_0('#skF_5'), B_468) | ~v13_waybel_0(B_468, '#skF_5') | ~m1_subset_1(B_468, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_467 | ~m1_subset_1(B_467, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_6, c_6473])).
% 19.24/10.04  tff(c_6523, plain, (![B_469]: (~r2_hidden(k3_yellow_0('#skF_5'), B_469) | ~v13_waybel_0(B_469, '#skF_5') | u1_struct_0('#skF_5')=B_469 | ~m1_subset_1(B_469, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_6482, c_4])).
% 19.24/10.04  tff(c_6534, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_46, c_6523])).
% 19.24/10.04  tff(c_6542, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_140, c_6534])).
% 19.24/10.04  tff(c_331, plain, (![A_69]: (k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_69))=A_69 | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(A_69, '#skF_6'))), inference(resolution, [status(thm)], [c_170, c_320])).
% 19.24/10.04  tff(c_340, plain, (![A_69]: (k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_69))=A_69 | v2_struct_0('#skF_5') | ~r2_hidden(A_69, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_331])).
% 19.24/10.04  tff(c_341, plain, (![A_69]: (k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_69))=A_69 | ~r2_hidden(A_69, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_340])).
% 19.24/10.04  tff(c_2316, plain, (![B_266, B_267]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_266))), B_267) | ~r2_hidden(k3_yellow_0('#skF_5'), B_267) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_266), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_267, '#skF_5') | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_266))) | u1_struct_0('#skF_5')=B_266 | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_932])).
% 19.24/10.04  tff(c_2343, plain, (![B_3, B_267]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_3), B_267) | ~r2_hidden(k3_yellow_0('#skF_5'), B_267) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_267, '#skF_5') | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_337, c_2316])).
% 19.24/10.04  tff(c_2360, plain, (![B_3, B_267]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_3), B_267) | ~r2_hidden(k3_yellow_0('#skF_5'), B_267) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_267, '#skF_5') | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_2343])).
% 19.24/10.04  tff(c_2362, plain, (![B_268, B_269]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_268), B_269) | ~r2_hidden(k3_yellow_0('#skF_5'), B_269) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_268), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_269, '#skF_5') | ~m1_subset_1(B_269, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_268))) | u1_struct_0('#skF_5')=B_268 | ~m1_subset_1(B_268, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_2360])).
% 19.24/10.04  tff(c_2365, plain, (![B_268, B_269]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_268), B_269) | ~r2_hidden(k3_yellow_0('#skF_5'), B_269) | ~v13_waybel_0(B_269, '#skF_5') | ~m1_subset_1(B_269, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_268 | ~m1_subset_1(B_268, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_268), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_2362])).
% 19.24/10.04  tff(c_2368, plain, (![B_268, B_269]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_268), B_269) | ~r2_hidden(k3_yellow_0('#skF_5'), B_269) | ~v13_waybel_0(B_269, '#skF_5') | ~m1_subset_1(B_269, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_268 | ~m1_subset_1(B_268, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_268), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_2365])).
% 19.24/10.04  tff(c_2370, plain, (![B_270, B_271]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_270), B_271) | ~r2_hidden(k3_yellow_0('#skF_5'), B_271) | ~v13_waybel_0(B_271, '#skF_5') | ~m1_subset_1(B_271, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_270 | ~m1_subset_1(B_270, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_270), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_2368])).
% 19.24/10.04  tff(c_2379, plain, (![B_272, B_273]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_272), B_273) | ~r2_hidden(k3_yellow_0('#skF_5'), B_273) | ~v13_waybel_0(B_273, '#skF_5') | ~m1_subset_1(B_273, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_272 | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_6, c_2370])).
% 19.24/10.04  tff(c_2406, plain, (![B_274]: (~r2_hidden(k3_yellow_0('#skF_5'), B_274) | ~v13_waybel_0(B_274, '#skF_5') | u1_struct_0('#skF_5')=B_274 | ~m1_subset_1(B_274, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_2379, c_4])).
% 19.24/10.04  tff(c_2417, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_46, c_2406])).
% 19.24/10.04  tff(c_2424, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_140, c_2417])).
% 19.24/10.04  tff(c_36, plain, (![A_20, B_34]: (m1_subset_1('#skF_3'(A_20, B_34), u1_struct_0(A_20)) | v13_waybel_0(B_34, A_20) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_105])).
% 19.24/10.04  tff(c_211, plain, (![A_83, B_84]: (r2_hidden('#skF_3'(A_83, B_84), B_84) | v13_waybel_0(B_84, A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_orders_2(A_83))), inference(cnfTransformation, [status(thm)], [f_105])).
% 19.24/10.04  tff(c_239, plain, (![A_87]: (r2_hidden('#skF_3'(A_87, u1_struct_0(A_87)), u1_struct_0(A_87)) | v13_waybel_0(u1_struct_0(A_87), A_87) | ~l1_orders_2(A_87))), inference(resolution, [status(thm)], [c_156, c_211])).
% 19.24/10.04  tff(c_172, plain, (![A_73]: (m1_subset_1(A_73, k1_zfmisc_1(A_73)))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_10])).
% 19.24/10.04  tff(c_14, plain, (![A_9, C_11, B_10]: (m1_subset_1(A_9, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 19.24/10.04  tff(c_178, plain, (![A_9, A_73]: (m1_subset_1(A_9, A_73) | ~r2_hidden(A_9, A_73))), inference(resolution, [status(thm)], [c_172, c_14])).
% 19.24/10.04  tff(c_243, plain, (![A_87]: (m1_subset_1('#skF_3'(A_87, u1_struct_0(A_87)), u1_struct_0(A_87)) | v13_waybel_0(u1_struct_0(A_87), A_87) | ~l1_orders_2(A_87))), inference(resolution, [status(thm)], [c_239, c_178])).
% 19.24/10.04  tff(c_508, plain, (![A_130]: (k1_yellow_0(A_130, k5_waybel_0(A_130, '#skF_3'(A_130, u1_struct_0(A_130))))='#skF_3'(A_130, u1_struct_0(A_130)) | ~v5_orders_2(A_130) | ~v4_orders_2(A_130) | ~v3_orders_2(A_130) | v2_struct_0(A_130) | v13_waybel_0(u1_struct_0(A_130), A_130) | ~l1_orders_2(A_130))), inference(resolution, [status(thm)], [c_243, c_320])).
% 19.24/10.04  tff(c_531, plain, (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), '#skF_3'('#skF_5', u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_3'('#skF_5', u1_struct_0('#skF_5')))) | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5') | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_508, c_312])).
% 19.24/10.04  tff(c_560, plain, (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), '#skF_3'('#skF_5', u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_3'('#skF_5', u1_struct_0('#skF_5')))) | v2_struct_0('#skF_5') | v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_62, c_60, c_58, c_531])).
% 19.24/10.04  tff(c_561, plain, (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), '#skF_3'('#skF_5', u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_3'('#skF_5', u1_struct_0('#skF_5')))) | v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_560])).
% 19.24/10.04  tff(c_567, plain, (~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_3'('#skF_5', u1_struct_0('#skF_5'))))), inference(splitLeft, [status(thm)], [c_561])).
% 19.24/10.04  tff(c_590, plain, (~m1_subset_1('#skF_3'('#skF_5', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_567])).
% 19.24/10.04  tff(c_593, plain, (~m1_subset_1('#skF_3'('#skF_5', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_590])).
% 19.24/10.04  tff(c_594, plain, (~m1_subset_1('#skF_3'('#skF_5', u1_struct_0('#skF_5')), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_593])).
% 19.24/10.04  tff(c_597, plain, (v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_36, c_594])).
% 19.24/10.04  tff(c_606, plain, (v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_156, c_597])).
% 19.24/10.04  tff(c_955, plain, (![C_148, B_149]: (r2_hidden(k1_yellow_0('#skF_5', C_148), B_149) | ~r2_hidden(k3_yellow_0('#skF_5'), B_149) | ~v13_waybel_0(B_149, '#skF_5') | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', C_148) | ~r2_hidden(k1_yellow_0('#skF_5', C_148), '#skF_6'))), inference(resolution, [status(thm)], [c_170, c_907])).
% 19.24/10.04  tff(c_961, plain, (![C_148]: (r2_hidden(k1_yellow_0('#skF_5', C_148), u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5') | ~r1_yellow_0('#skF_5', C_148) | ~r2_hidden(k1_yellow_0('#skF_5', C_148), '#skF_6'))), inference(resolution, [status(thm)], [c_156, c_955])).
% 19.24/10.04  tff(c_967, plain, (![C_148]: (r2_hidden(k1_yellow_0('#skF_5', C_148), u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', C_148) | ~r2_hidden(k1_yellow_0('#skF_5', C_148), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_606, c_961])).
% 19.24/10.04  tff(c_971, plain, (~r2_hidden(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_967])).
% 19.24/10.04  tff(c_2464, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2424, c_971])).
% 19.24/10.04  tff(c_2480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_2464])).
% 19.24/10.04  tff(c_2501, plain, (![C_278]: (r2_hidden(k1_yellow_0('#skF_5', C_278), u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', C_278) | ~r2_hidden(k1_yellow_0('#skF_5', C_278), '#skF_6'))), inference(splitRight, [status(thm)], [c_967])).
% 19.24/10.04  tff(c_2547, plain, (![A_279]: (r2_hidden(A_279, u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_279)) | ~r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_279)), '#skF_6') | ~r2_hidden(A_279, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_341, c_2501])).
% 19.24/10.04  tff(c_2627, plain, (![A_281]: (r2_hidden(A_281, u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_281)) | ~r2_hidden(A_281, '#skF_6') | ~r2_hidden(A_281, '#skF_6') | ~r2_hidden(A_281, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_341, c_2547])).
% 19.24/10.04  tff(c_2663, plain, (![A_283]: (u1_struct_0('#skF_5')=A_283 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_283)) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(A_283, u1_struct_0('#skF_5')))) | ~r2_hidden('#skF_1'(A_283, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_2627, c_4])).
% 19.24/10.04  tff(c_2666, plain, (![A_283]: (u1_struct_0('#skF_5')=A_283 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_283)) | ~r2_hidden('#skF_1'(A_283, u1_struct_0('#skF_5')), '#skF_6') | ~m1_subset_1('#skF_1'(A_283, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_2663])).
% 19.24/10.04  tff(c_2669, plain, (![A_283]: (u1_struct_0('#skF_5')=A_283 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_283)) | ~r2_hidden('#skF_1'(A_283, u1_struct_0('#skF_5')), '#skF_6') | ~m1_subset_1('#skF_1'(A_283, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_2666])).
% 19.24/10.04  tff(c_2671, plain, (![A_284]: (u1_struct_0('#skF_5')=A_284 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_284)) | ~r2_hidden('#skF_1'(A_284, u1_struct_0('#skF_5')), '#skF_6') | ~m1_subset_1('#skF_1'(A_284, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_2669])).
% 19.24/10.04  tff(c_2684, plain, (![A_285]: (u1_struct_0('#skF_5')=A_285 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_285)) | ~r2_hidden('#skF_1'(A_285, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_170, c_2671])).
% 19.24/10.04  tff(c_2687, plain, (![A_285]: (u1_struct_0('#skF_5')=A_285 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_285)) | v1_xboole_0('#skF_6') | ~m1_subset_1('#skF_1'(A_285, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_12, c_2684])).
% 19.24/10.04  tff(c_2729, plain, (![A_290]: (u1_struct_0('#skF_5')=A_290 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_290)) | ~m1_subset_1('#skF_1'(A_290, u1_struct_0('#skF_5')), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_2687])).
% 19.24/10.04  tff(c_2734, plain, (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_6, c_2729])).
% 19.24/10.04  tff(c_2735, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_2734])).
% 19.24/10.04  tff(c_6611, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6542, c_2735])).
% 19.24/10.04  tff(c_6635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_6611])).
% 19.24/10.04  tff(c_6636, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_2734])).
% 19.24/10.04  tff(c_204, plain, (![A_80, B_81]: (~r2_hidden('#skF_1'(A_80, B_81), B_81) | B_81=A_80 | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 19.24/10.04  tff(c_225, plain, (![B_85, A_86]: (B_85=A_86 | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)) | v1_xboole_0(B_85) | ~m1_subset_1('#skF_1'(A_86, B_85), B_85))), inference(resolution, [status(thm)], [c_12, c_204])).
% 19.24/10.04  tff(c_238, plain, (![A_86]: (u1_struct_0('#skF_5')=A_86 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_86)) | v1_xboole_0(u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'(A_86, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_170, c_225])).
% 19.24/10.04  tff(c_245, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_238])).
% 19.24/10.04  tff(c_6659, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6636, c_245])).
% 19.24/10.04  tff(c_6667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_6659])).
% 19.24/10.04  tff(c_6668, plain, (v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5') | r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), '#skF_3'('#skF_5', u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_561])).
% 19.24/10.04  tff(c_6670, plain, (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), '#skF_3'('#skF_5', u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_6668])).
% 19.24/10.04  tff(c_26, plain, (![D_43, B_34, A_20, C_41]: (r2_hidden(D_43, B_34) | ~r1_orders_2(A_20, C_41, D_43) | ~r2_hidden(C_41, B_34) | ~m1_subset_1(D_43, u1_struct_0(A_20)) | ~m1_subset_1(C_41, u1_struct_0(A_20)) | ~v13_waybel_0(B_34, A_20) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_105])).
% 19.24/10.04  tff(c_6692, plain, (![B_34]: (r2_hidden('#skF_3'('#skF_5', u1_struct_0('#skF_5')), B_34) | ~r2_hidden(k3_yellow_0('#skF_5'), B_34) | ~m1_subset_1('#skF_3'('#skF_5', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_34, '#skF_5') | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_6670, c_26])).
% 19.24/10.04  tff(c_6695, plain, (![B_34]: (r2_hidden('#skF_3'('#skF_5', u1_struct_0('#skF_5')), B_34) | ~r2_hidden(k3_yellow_0('#skF_5'), B_34) | ~m1_subset_1('#skF_3'('#skF_5', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_34, '#skF_5') | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6692])).
% 19.24/10.04  tff(c_6879, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_6695])).
% 19.24/10.04  tff(c_6882, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_170, c_6879])).
% 19.24/10.04  tff(c_6889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_6882])).
% 19.24/10.04  tff(c_6891, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_6695])).
% 19.24/10.04  tff(c_7043, plain, (![C_488, B_489]: (r2_hidden(k1_yellow_0('#skF_5', C_488), B_489) | ~r2_hidden(k3_yellow_0('#skF_5'), B_489) | ~m1_subset_1(k1_yellow_0('#skF_5', C_488), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_489, '#skF_5') | ~m1_subset_1(B_489, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', C_488))), inference(demodulation, [status(thm), theory('equality')], [c_6891, c_484])).
% 19.24/10.04  tff(c_7048, plain, (![B_3, B_489]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))), B_489) | ~r2_hidden(k3_yellow_0('#skF_5'), B_489) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_489, '#skF_5') | ~m1_subset_1(B_489, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_337, c_7043])).
% 19.24/10.04  tff(c_7068, plain, (![B_3, B_489]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))), B_489) | ~r2_hidden(k3_yellow_0('#skF_5'), B_489) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_489, '#skF_5') | ~m1_subset_1(B_489, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_7048])).
% 19.24/10.04  tff(c_11656, plain, (![B_764, B_765]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_764))), B_765) | ~r2_hidden(k3_yellow_0('#skF_5'), B_765) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_764), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_765, '#skF_5') | ~m1_subset_1(B_765, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_764))) | u1_struct_0('#skF_5')=B_764 | ~m1_subset_1(B_764, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_7068])).
% 19.24/10.04  tff(c_11691, plain, (![B_3, B_765]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_3), B_765) | ~r2_hidden(k3_yellow_0('#skF_5'), B_765) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_765, '#skF_5') | ~m1_subset_1(B_765, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_337, c_11656])).
% 19.24/10.04  tff(c_11714, plain, (![B_3, B_765]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_3), B_765) | ~r2_hidden(k3_yellow_0('#skF_5'), B_765) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_765, '#skF_5') | ~m1_subset_1(B_765, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_11691])).
% 19.24/10.04  tff(c_11716, plain, (![B_766, B_767]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_766), B_767) | ~r2_hidden(k3_yellow_0('#skF_5'), B_767) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_766), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_767, '#skF_5') | ~m1_subset_1(B_767, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_766))) | u1_struct_0('#skF_5')=B_766 | ~m1_subset_1(B_766, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_11714])).
% 19.24/10.04  tff(c_11719, plain, (![B_766, B_767]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_766), B_767) | ~r2_hidden(k3_yellow_0('#skF_5'), B_767) | ~v13_waybel_0(B_767, '#skF_5') | ~m1_subset_1(B_767, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_766 | ~m1_subset_1(B_766, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_766), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_11716])).
% 19.24/10.04  tff(c_11722, plain, (![B_766, B_767]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_766), B_767) | ~r2_hidden(k3_yellow_0('#skF_5'), B_767) | ~v13_waybel_0(B_767, '#skF_5') | ~m1_subset_1(B_767, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_766 | ~m1_subset_1(B_766, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_766), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_11719])).
% 19.24/10.04  tff(c_11724, plain, (![B_768, B_769]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_768), B_769) | ~r2_hidden(k3_yellow_0('#skF_5'), B_769) | ~v13_waybel_0(B_769, '#skF_5') | ~m1_subset_1(B_769, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_768 | ~m1_subset_1(B_768, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_768), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_11722])).
% 19.24/10.04  tff(c_11733, plain, (![B_770, B_771]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_770), B_771) | ~r2_hidden(k3_yellow_0('#skF_5'), B_771) | ~v13_waybel_0(B_771, '#skF_5') | ~m1_subset_1(B_771, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_770 | ~m1_subset_1(B_770, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_6, c_11724])).
% 19.24/10.04  tff(c_11768, plain, (![B_772]: (~r2_hidden(k3_yellow_0('#skF_5'), B_772) | ~v13_waybel_0(B_772, '#skF_5') | u1_struct_0('#skF_5')=B_772 | ~m1_subset_1(B_772, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_11733, c_4])).
% 19.24/10.04  tff(c_11779, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_46, c_11768])).
% 19.24/10.04  tff(c_11787, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_140, c_11779])).
% 19.24/10.04  tff(c_8140, plain, (![B_592, B_593]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_592))), B_593) | ~r2_hidden(k3_yellow_0('#skF_5'), B_593) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_592), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_593, '#skF_5') | ~m1_subset_1(B_593, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_592))) | u1_struct_0('#skF_5')=B_592 | ~m1_subset_1(B_592, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_7068])).
% 19.24/10.04  tff(c_8163, plain, (![B_3, B_593]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_3), B_593) | ~r2_hidden(k3_yellow_0('#skF_5'), B_593) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_593, '#skF_5') | ~m1_subset_1(B_593, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_337, c_8140])).
% 19.24/10.04  tff(c_8178, plain, (![B_3, B_593]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_3), B_593) | ~r2_hidden(k3_yellow_0('#skF_5'), B_593) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_593, '#skF_5') | ~m1_subset_1(B_593, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_8163])).
% 19.24/10.04  tff(c_8180, plain, (![B_594, B_595]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_594), B_595) | ~r2_hidden(k3_yellow_0('#skF_5'), B_595) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_594), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_595, '#skF_5') | ~m1_subset_1(B_595, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_594))) | u1_struct_0('#skF_5')=B_594 | ~m1_subset_1(B_594, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_8178])).
% 19.24/10.04  tff(c_8183, plain, (![B_594, B_595]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_594), B_595) | ~r2_hidden(k3_yellow_0('#skF_5'), B_595) | ~v13_waybel_0(B_595, '#skF_5') | ~m1_subset_1(B_595, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_594 | ~m1_subset_1(B_594, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_594), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_8180])).
% 19.24/10.04  tff(c_8186, plain, (![B_594, B_595]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_594), B_595) | ~r2_hidden(k3_yellow_0('#skF_5'), B_595) | ~v13_waybel_0(B_595, '#skF_5') | ~m1_subset_1(B_595, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_594 | ~m1_subset_1(B_594, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_594), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_8183])).
% 19.24/10.04  tff(c_8188, plain, (![B_596, B_597]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_596), B_597) | ~r2_hidden(k3_yellow_0('#skF_5'), B_597) | ~v13_waybel_0(B_597, '#skF_5') | ~m1_subset_1(B_597, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_596 | ~m1_subset_1(B_596, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_596), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_8186])).
% 19.24/10.04  tff(c_8197, plain, (![B_598, B_599]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_598), B_599) | ~r2_hidden(k3_yellow_0('#skF_5'), B_599) | ~v13_waybel_0(B_599, '#skF_5') | ~m1_subset_1(B_599, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_598 | ~m1_subset_1(B_598, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_6, c_8188])).
% 19.24/10.04  tff(c_8221, plain, (![B_600]: (~r2_hidden(k3_yellow_0('#skF_5'), B_600) | ~v13_waybel_0(B_600, '#skF_5') | u1_struct_0('#skF_5')=B_600 | ~m1_subset_1(B_600, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_8197, c_4])).
% 19.24/10.04  tff(c_8232, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_46, c_8221])).
% 19.24/10.04  tff(c_8239, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_140, c_8232])).
% 19.24/10.04  tff(c_34, plain, (![A_20, B_34]: (m1_subset_1('#skF_4'(A_20, B_34), u1_struct_0(A_20)) | v13_waybel_0(B_34, A_20) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_105])).
% 19.24/10.04  tff(c_6697, plain, (![A_473, B_474]: (k1_yellow_0(A_473, k5_waybel_0(A_473, '#skF_4'(A_473, B_474)))='#skF_4'(A_473, B_474) | ~v5_orders_2(A_473) | ~v4_orders_2(A_473) | ~v3_orders_2(A_473) | v2_struct_0(A_473) | v13_waybel_0(B_474, A_473) | ~m1_subset_1(B_474, k1_zfmisc_1(u1_struct_0(A_473))) | ~l1_orders_2(A_473))), inference(resolution, [status(thm)], [c_34, c_320])).
% 19.24/10.04  tff(c_6712, plain, (![A_475]: (k1_yellow_0(A_475, k5_waybel_0(A_475, '#skF_4'(A_475, u1_struct_0(A_475))))='#skF_4'(A_475, u1_struct_0(A_475)) | ~v5_orders_2(A_475) | ~v4_orders_2(A_475) | ~v3_orders_2(A_475) | v2_struct_0(A_475) | v13_waybel_0(u1_struct_0(A_475), A_475) | ~l1_orders_2(A_475))), inference(resolution, [status(thm)], [c_156, c_6697])).
% 19.24/10.04  tff(c_6735, plain, (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), '#skF_4'('#skF_5', u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_4'('#skF_5', u1_struct_0('#skF_5')))) | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5') | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6712, c_312])).
% 19.24/10.04  tff(c_6764, plain, (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), '#skF_4'('#skF_5', u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_4'('#skF_5', u1_struct_0('#skF_5')))) | v2_struct_0('#skF_5') | v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_62, c_60, c_58, c_6735])).
% 19.24/10.04  tff(c_6765, plain, (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), '#skF_4'('#skF_5', u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_4'('#skF_5', u1_struct_0('#skF_5')))) | v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_6764])).
% 19.24/10.04  tff(c_6771, plain, (~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_4'('#skF_5', u1_struct_0('#skF_5'))))), inference(splitLeft, [status(thm)], [c_6765])).
% 19.24/10.04  tff(c_6774, plain, (~m1_subset_1('#skF_4'('#skF_5', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_6771])).
% 19.24/10.04  tff(c_6777, plain, (~m1_subset_1('#skF_4'('#skF_5', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_6774])).
% 19.24/10.04  tff(c_6778, plain, (~m1_subset_1('#skF_4'('#skF_5', u1_struct_0('#skF_5')), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_6777])).
% 19.24/10.04  tff(c_6781, plain, (v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_34, c_6778])).
% 19.24/10.04  tff(c_6787, plain, (v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_156, c_6781])).
% 19.24/10.04  tff(c_7082, plain, (![C_490, B_491]: (r2_hidden(k1_yellow_0('#skF_5', C_490), B_491) | ~r2_hidden(k3_yellow_0('#skF_5'), B_491) | ~v13_waybel_0(B_491, '#skF_5') | ~m1_subset_1(B_491, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', C_490) | ~r2_hidden(k1_yellow_0('#skF_5', C_490), '#skF_6'))), inference(resolution, [status(thm)], [c_170, c_7043])).
% 19.24/10.04  tff(c_7088, plain, (![C_490]: (r2_hidden(k1_yellow_0('#skF_5', C_490), u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5') | ~r1_yellow_0('#skF_5', C_490) | ~r2_hidden(k1_yellow_0('#skF_5', C_490), '#skF_6'))), inference(resolution, [status(thm)], [c_156, c_7082])).
% 19.24/10.04  tff(c_7094, plain, (![C_490]: (r2_hidden(k1_yellow_0('#skF_5', C_490), u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', C_490) | ~r2_hidden(k1_yellow_0('#skF_5', C_490), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6787, c_7088])).
% 19.24/10.04  tff(c_7098, plain, (~r2_hidden(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_7094])).
% 19.24/10.04  tff(c_8273, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8239, c_7098])).
% 19.24/10.04  tff(c_8294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_8273])).
% 19.24/10.04  tff(c_8315, plain, (![C_604]: (r2_hidden(k1_yellow_0('#skF_5', C_604), u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', C_604) | ~r2_hidden(k1_yellow_0('#skF_5', C_604), '#skF_6'))), inference(splitRight, [status(thm)], [c_7094])).
% 19.24/10.04  tff(c_8361, plain, (![A_605]: (r2_hidden(A_605, u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_605)) | ~r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_605)), '#skF_6') | ~r2_hidden(A_605, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_341, c_8315])).
% 19.24/10.04  tff(c_8441, plain, (![A_607]: (r2_hidden(A_607, u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_607)) | ~r2_hidden(A_607, '#skF_6') | ~r2_hidden(A_607, '#skF_6') | ~r2_hidden(A_607, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_341, c_8361])).
% 19.24/10.04  tff(c_8477, plain, (![A_609]: (u1_struct_0('#skF_5')=A_609 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_609)) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(A_609, u1_struct_0('#skF_5')))) | ~r2_hidden('#skF_1'(A_609, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_8441, c_4])).
% 19.24/10.04  tff(c_8480, plain, (![A_609]: (u1_struct_0('#skF_5')=A_609 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_609)) | ~r2_hidden('#skF_1'(A_609, u1_struct_0('#skF_5')), '#skF_6') | ~m1_subset_1('#skF_1'(A_609, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_8477])).
% 19.24/10.04  tff(c_8483, plain, (![A_609]: (u1_struct_0('#skF_5')=A_609 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_609)) | ~r2_hidden('#skF_1'(A_609, u1_struct_0('#skF_5')), '#skF_6') | ~m1_subset_1('#skF_1'(A_609, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_8480])).
% 19.24/10.04  tff(c_8485, plain, (![A_610]: (u1_struct_0('#skF_5')=A_610 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_610)) | ~r2_hidden('#skF_1'(A_610, u1_struct_0('#skF_5')), '#skF_6') | ~m1_subset_1('#skF_1'(A_610, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_8483])).
% 19.24/10.04  tff(c_8498, plain, (![A_611]: (u1_struct_0('#skF_5')=A_611 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_611)) | ~r2_hidden('#skF_1'(A_611, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_170, c_8485])).
% 19.24/10.04  tff(c_8501, plain, (![A_611]: (u1_struct_0('#skF_5')=A_611 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_611)) | v1_xboole_0('#skF_6') | ~m1_subset_1('#skF_1'(A_611, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_12, c_8498])).
% 19.24/10.04  tff(c_8543, plain, (![A_616]: (u1_struct_0('#skF_5')=A_616 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_616)) | ~m1_subset_1('#skF_1'(A_616, u1_struct_0('#skF_5')), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_8501])).
% 19.24/10.04  tff(c_8548, plain, (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_6, c_8543])).
% 19.24/10.04  tff(c_8549, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_8548])).
% 19.24/10.04  tff(c_11851, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_11787, c_8549])).
% 19.24/10.04  tff(c_11880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_11851])).
% 19.24/10.04  tff(c_11881, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_8548])).
% 19.24/10.04  tff(c_11939, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11881, c_245])).
% 19.24/10.04  tff(c_11947, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_11939])).
% 19.24/10.04  tff(c_11948, plain, (v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5') | r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), '#skF_4'('#skF_5', u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_6765])).
% 19.24/10.04  tff(c_11950, plain, (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), '#skF_4'('#skF_5', u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_11948])).
% 19.24/10.04  tff(c_11955, plain, (![B_34]: (r2_hidden('#skF_4'('#skF_5', u1_struct_0('#skF_5')), B_34) | ~r2_hidden(k3_yellow_0('#skF_5'), B_34) | ~m1_subset_1('#skF_4'('#skF_5', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_34, '#skF_5') | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_11950, c_26])).
% 19.24/10.04  tff(c_11958, plain, (![B_34]: (r2_hidden('#skF_4'('#skF_5', u1_struct_0('#skF_5')), B_34) | ~r2_hidden(k3_yellow_0('#skF_5'), B_34) | ~m1_subset_1('#skF_4'('#skF_5', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_34, '#skF_5') | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_11955])).
% 19.24/10.04  tff(c_12049, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_11958])).
% 19.24/10.04  tff(c_12052, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_170, c_12049])).
% 19.24/10.04  tff(c_12059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_12052])).
% 19.24/10.04  tff(c_12061, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_11958])).
% 19.24/10.04  tff(c_20, plain, (![A_14, B_17, C_18]: (r1_orders_2(A_14, k1_yellow_0(A_14, B_17), k1_yellow_0(A_14, C_18)) | ~r1_yellow_0(A_14, C_18) | ~r1_yellow_0(A_14, B_17) | ~r1_tarski(B_17, C_18) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.24/10.04  tff(c_23559, plain, (![A_1424, C_1425, B_1426, B_1427]: (r2_hidden(k1_yellow_0(A_1424, C_1425), B_1426) | ~r2_hidden(k1_yellow_0(A_1424, B_1427), B_1426) | ~m1_subset_1(k1_yellow_0(A_1424, C_1425), u1_struct_0(A_1424)) | ~m1_subset_1(k1_yellow_0(A_1424, B_1427), u1_struct_0(A_1424)) | ~v13_waybel_0(B_1426, A_1424) | ~m1_subset_1(B_1426, k1_zfmisc_1(u1_struct_0(A_1424))) | ~r1_yellow_0(A_1424, C_1425) | ~r1_yellow_0(A_1424, B_1427) | ~r1_tarski(B_1427, C_1425) | ~l1_orders_2(A_1424))), inference(resolution, [status(thm)], [c_20, c_450])).
% 19.24/10.04  tff(c_23578, plain, (![C_1425, B_1426]: (r2_hidden(k1_yellow_0('#skF_5', C_1425), B_1426) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1426) | ~m1_subset_1(k1_yellow_0('#skF_5', C_1425), u1_struct_0('#skF_5')) | ~m1_subset_1(k1_yellow_0('#skF_5', k1_xboole_0), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1426, '#skF_5') | ~m1_subset_1(B_1426, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', C_1425) | ~r1_yellow_0('#skF_5', k1_xboole_0) | ~r1_tarski(k1_xboole_0, C_1425) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_23559])).
% 19.24/10.04  tff(c_23592, plain, (![C_1429, B_1430]: (r2_hidden(k1_yellow_0('#skF_5', C_1429), B_1430) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1430) | ~m1_subset_1(k1_yellow_0('#skF_5', C_1429), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1430, '#skF_5') | ~m1_subset_1(B_1430, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', C_1429))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2, c_313, c_12061, c_81, c_23578])).
% 19.24/10.04  tff(c_23599, plain, (![B_3, B_1430]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))), B_1430) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1430) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1430, '#skF_5') | ~m1_subset_1(B_1430, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_337, c_23592])).
% 19.24/10.04  tff(c_23621, plain, (![B_3, B_1430]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))), B_1430) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1430) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1430, '#skF_5') | ~m1_subset_1(B_1430, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_23599])).
% 19.24/10.04  tff(c_25872, plain, (![B_1599, B_1600]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_1599))), B_1600) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1600) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1599), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1600, '#skF_5') | ~m1_subset_1(B_1600, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_1599))) | u1_struct_0('#skF_5')=B_1599 | ~m1_subset_1(B_1599, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_23621])).
% 19.24/10.04  tff(c_25899, plain, (![B_3, B_1600]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_3), B_1600) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1600) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1600, '#skF_5') | ~m1_subset_1(B_1600, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_337, c_25872])).
% 19.24/10.04  tff(c_25916, plain, (![B_3, B_1600]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_3), B_1600) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1600) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1600, '#skF_5') | ~m1_subset_1(B_1600, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_25899])).
% 19.24/10.04  tff(c_25918, plain, (![B_1601, B_1602]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1601), B_1602) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1602) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1601), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1602, '#skF_5') | ~m1_subset_1(B_1602, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_1601))) | u1_struct_0('#skF_5')=B_1601 | ~m1_subset_1(B_1601, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_25916])).
% 19.24/10.04  tff(c_25921, plain, (![B_1601, B_1602]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1601), B_1602) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1602) | ~v13_waybel_0(B_1602, '#skF_5') | ~m1_subset_1(B_1602, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_1601 | ~m1_subset_1(B_1601, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1601), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_25918])).
% 19.24/10.04  tff(c_25924, plain, (![B_1601, B_1602]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1601), B_1602) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1602) | ~v13_waybel_0(B_1602, '#skF_5') | ~m1_subset_1(B_1602, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_1601 | ~m1_subset_1(B_1601, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1601), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_25921])).
% 19.24/10.04  tff(c_25926, plain, (![B_1603, B_1604]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1603), B_1604) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1604) | ~v13_waybel_0(B_1604, '#skF_5') | ~m1_subset_1(B_1604, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_1603 | ~m1_subset_1(B_1603, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1603), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_25924])).
% 19.24/10.04  tff(c_25935, plain, (![B_1605, B_1606]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1605), B_1606) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1606) | ~v13_waybel_0(B_1606, '#skF_5') | ~m1_subset_1(B_1606, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_1605 | ~m1_subset_1(B_1605, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_6, c_25926])).
% 19.24/10.04  tff(c_25965, plain, (![B_1607]: (~r2_hidden(k3_yellow_0('#skF_5'), B_1607) | ~v13_waybel_0(B_1607, '#skF_5') | u1_struct_0('#skF_5')=B_1607 | ~m1_subset_1(B_1607, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_25935, c_4])).
% 19.24/10.04  tff(c_25976, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_46, c_25965])).
% 19.24/10.04  tff(c_25981, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_140, c_25976])).
% 19.24/10.04  tff(c_17227, plain, (![A_1069, C_1070, B_1071, B_1072]: (r2_hidden(k1_yellow_0(A_1069, C_1070), B_1071) | ~r2_hidden(k1_yellow_0(A_1069, B_1072), B_1071) | ~m1_subset_1(k1_yellow_0(A_1069, C_1070), u1_struct_0(A_1069)) | ~m1_subset_1(k1_yellow_0(A_1069, B_1072), u1_struct_0(A_1069)) | ~v13_waybel_0(B_1071, A_1069) | ~m1_subset_1(B_1071, k1_zfmisc_1(u1_struct_0(A_1069))) | ~r1_yellow_0(A_1069, C_1070) | ~r1_yellow_0(A_1069, B_1072) | ~r1_tarski(B_1072, C_1070) | ~l1_orders_2(A_1069))), inference(resolution, [status(thm)], [c_20, c_450])).
% 19.24/10.04  tff(c_17246, plain, (![C_1070, B_1071]: (r2_hidden(k1_yellow_0('#skF_5', C_1070), B_1071) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1071) | ~m1_subset_1(k1_yellow_0('#skF_5', C_1070), u1_struct_0('#skF_5')) | ~m1_subset_1(k1_yellow_0('#skF_5', k1_xboole_0), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1071, '#skF_5') | ~m1_subset_1(B_1071, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', C_1070) | ~r1_yellow_0('#skF_5', k1_xboole_0) | ~r1_tarski(k1_xboole_0, C_1070) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_17227])).
% 19.24/10.04  tff(c_17256, plain, (![C_1073, B_1074]: (r2_hidden(k1_yellow_0('#skF_5', C_1073), B_1074) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1074) | ~m1_subset_1(k1_yellow_0('#skF_5', C_1073), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1074, '#skF_5') | ~m1_subset_1(B_1074, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', C_1073))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2, c_313, c_12061, c_81, c_17246])).
% 19.24/10.04  tff(c_17263, plain, (![B_3, B_1074]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))), B_1074) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1074) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1074, '#skF_5') | ~m1_subset_1(B_1074, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_337, c_17256])).
% 19.24/10.04  tff(c_17285, plain, (![B_3, B_1074]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))), B_1074) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1074) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1074, '#skF_5') | ~m1_subset_1(B_1074, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_17263])).
% 19.24/10.04  tff(c_23045, plain, (![B_1404, B_1405]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_1404))), B_1405) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1405) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1404), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1405, '#skF_5') | ~m1_subset_1(B_1405, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_1404))) | u1_struct_0('#skF_5')=B_1404 | ~m1_subset_1(B_1404, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_17285])).
% 19.24/10.04  tff(c_23082, plain, (![B_3, B_1405]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_3), B_1405) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1405) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1405, '#skF_5') | ~m1_subset_1(B_1405, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_337, c_23045])).
% 19.24/10.04  tff(c_23106, plain, (![B_3, B_1405]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_3), B_1405) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1405) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1405, '#skF_5') | ~m1_subset_1(B_1405, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_23082])).
% 19.24/10.04  tff(c_23108, plain, (![B_1406, B_1407]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1406), B_1407) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1407) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1406), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1407, '#skF_5') | ~m1_subset_1(B_1407, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_1406))) | u1_struct_0('#skF_5')=B_1406 | ~m1_subset_1(B_1406, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_23106])).
% 19.24/10.04  tff(c_23111, plain, (![B_1406, B_1407]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1406), B_1407) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1407) | ~v13_waybel_0(B_1407, '#skF_5') | ~m1_subset_1(B_1407, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_1406 | ~m1_subset_1(B_1406, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1406), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_23108])).
% 19.24/10.04  tff(c_23114, plain, (![B_1406, B_1407]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1406), B_1407) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1407) | ~v13_waybel_0(B_1407, '#skF_5') | ~m1_subset_1(B_1407, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_1406 | ~m1_subset_1(B_1406, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1406), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_23111])).
% 19.24/10.04  tff(c_23116, plain, (![B_1408, B_1409]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1408), B_1409) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1409) | ~v13_waybel_0(B_1409, '#skF_5') | ~m1_subset_1(B_1409, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_1408 | ~m1_subset_1(B_1408, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1408), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_23114])).
% 19.24/10.04  tff(c_23125, plain, (![B_1410, B_1411]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1410), B_1411) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1411) | ~v13_waybel_0(B_1411, '#skF_5') | ~m1_subset_1(B_1411, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_1410 | ~m1_subset_1(B_1410, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_6, c_23116])).
% 19.24/10.04  tff(c_23166, plain, (![B_1412]: (~r2_hidden(k3_yellow_0('#skF_5'), B_1412) | ~v13_waybel_0(B_1412, '#skF_5') | u1_struct_0('#skF_5')=B_1412 | ~m1_subset_1(B_1412, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_23125, c_4])).
% 19.24/10.04  tff(c_23177, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_46, c_23166])).
% 19.24/10.04  tff(c_23185, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_140, c_23177])).
% 19.24/10.04  tff(c_18916, plain, (![B_1208, B_1209]: (r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_1208))), B_1209) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1209) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1208), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1209, '#skF_5') | ~m1_subset_1(B_1209, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_1208))) | u1_struct_0('#skF_5')=B_1208 | ~m1_subset_1(B_1208, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_17285])).
% 19.24/10.04  tff(c_18943, plain, (![B_3, B_1209]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_3), B_1209) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1209) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1209, '#skF_5') | ~m1_subset_1(B_1209, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_337, c_18916])).
% 19.24/10.04  tff(c_18960, plain, (![B_3, B_1209]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_3), B_1209) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1209) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_3), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1209, '#skF_5') | ~m1_subset_1(B_1209, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_3))) | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_18943])).
% 19.24/10.04  tff(c_18962, plain, (![B_1210, B_1211]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1210), B_1211) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1211) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1210), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1211, '#skF_5') | ~m1_subset_1(B_1211, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(u1_struct_0('#skF_5'), B_1210))) | u1_struct_0('#skF_5')=B_1210 | ~m1_subset_1(B_1210, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_18960])).
% 19.24/10.04  tff(c_18965, plain, (![B_1210, B_1211]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1210), B_1211) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1211) | ~v13_waybel_0(B_1211, '#skF_5') | ~m1_subset_1(B_1211, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_1210 | ~m1_subset_1(B_1210, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1210), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_18962])).
% 19.24/10.04  tff(c_18968, plain, (![B_1210, B_1211]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1210), B_1211) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1211) | ~v13_waybel_0(B_1211, '#skF_5') | ~m1_subset_1(B_1211, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_1210 | ~m1_subset_1(B_1210, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1210), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_18965])).
% 19.24/10.04  tff(c_18970, plain, (![B_1212, B_1213]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1212), B_1213) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1213) | ~v13_waybel_0(B_1213, '#skF_5') | ~m1_subset_1(B_1213, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_1212 | ~m1_subset_1(B_1212, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_1212), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_18968])).
% 19.24/10.04  tff(c_18979, plain, (![B_1214, B_1215]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1214), B_1215) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1215) | ~v13_waybel_0(B_1215, '#skF_5') | ~m1_subset_1(B_1215, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_1214 | ~m1_subset_1(B_1214, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_6, c_18970])).
% 19.24/10.04  tff(c_19003, plain, (![B_1216]: (~r2_hidden(k3_yellow_0('#skF_5'), B_1216) | ~v13_waybel_0(B_1216, '#skF_5') | u1_struct_0('#skF_5')=B_1216 | ~m1_subset_1(B_1216, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_18979, c_4])).
% 19.24/10.04  tff(c_19014, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_46, c_19003])).
% 19.24/10.04  tff(c_19021, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_140, c_19014])).
% 19.24/10.04  tff(c_11949, plain, (r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_4'('#skF_5', u1_struct_0('#skF_5'))))), inference(splitRight, [status(thm)], [c_6765])).
% 19.24/10.04  tff(c_343, plain, (![A_112]: (k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_112))=A_112 | ~r2_hidden(A_112, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_340])).
% 19.24/10.04  tff(c_352, plain, (![A_112, C_18]: (r1_orders_2('#skF_5', A_112, k1_yellow_0('#skF_5', C_18)) | ~r1_yellow_0('#skF_5', C_18) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_112)) | ~r1_tarski(k5_waybel_0('#skF_5', A_112), C_18) | ~l1_orders_2('#skF_5') | ~r2_hidden(A_112, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_343, c_20])).
% 19.24/10.04  tff(c_361, plain, (![A_112, C_18]: (r1_orders_2('#skF_5', A_112, k1_yellow_0('#skF_5', C_18)) | ~r1_yellow_0('#skF_5', C_18) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_112)) | ~r1_tarski(k5_waybel_0('#skF_5', A_112), C_18) | ~r2_hidden(A_112, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_352])).
% 19.24/10.04  tff(c_6723, plain, (![A_112]: (r1_orders_2('#skF_5', A_112, '#skF_4'('#skF_5', u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_4'('#skF_5', u1_struct_0('#skF_5')))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_112)) | ~r1_tarski(k5_waybel_0('#skF_5', A_112), k5_waybel_0('#skF_5', '#skF_4'('#skF_5', u1_struct_0('#skF_5')))) | ~r2_hidden(A_112, '#skF_6') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5') | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6712, c_361])).
% 19.24/10.04  tff(c_6754, plain, (![A_112]: (r1_orders_2('#skF_5', A_112, '#skF_4'('#skF_5', u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_4'('#skF_5', u1_struct_0('#skF_5')))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_112)) | ~r1_tarski(k5_waybel_0('#skF_5', A_112), k5_waybel_0('#skF_5', '#skF_4'('#skF_5', u1_struct_0('#skF_5')))) | ~r2_hidden(A_112, '#skF_6') | v2_struct_0('#skF_5') | v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_62, c_60, c_58, c_6723])).
% 19.24/10.04  tff(c_6755, plain, (![A_112]: (r1_orders_2('#skF_5', A_112, '#skF_4'('#skF_5', u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_4'('#skF_5', u1_struct_0('#skF_5')))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_112)) | ~r1_tarski(k5_waybel_0('#skF_5', A_112), k5_waybel_0('#skF_5', '#skF_4'('#skF_5', u1_struct_0('#skF_5')))) | ~r2_hidden(A_112, '#skF_6') | v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_6754])).
% 19.24/10.04  tff(c_17071, plain, (![A_112]: (r1_orders_2('#skF_5', A_112, '#skF_4'('#skF_5', u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_112)) | ~r1_tarski(k5_waybel_0('#skF_5', A_112), k5_waybel_0('#skF_5', '#skF_4'('#skF_5', u1_struct_0('#skF_5')))) | ~r2_hidden(A_112, '#skF_6') | v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_11949, c_6755])).
% 19.24/10.04  tff(c_17072, plain, (v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_17071])).
% 19.24/10.04  tff(c_17299, plain, (![C_1075, B_1076]: (r2_hidden(k1_yellow_0('#skF_5', C_1075), B_1076) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1076) | ~v13_waybel_0(B_1076, '#skF_5') | ~m1_subset_1(B_1076, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', C_1075) | ~r2_hidden(k1_yellow_0('#skF_5', C_1075), '#skF_6'))), inference(resolution, [status(thm)], [c_170, c_17256])).
% 19.24/10.04  tff(c_17305, plain, (![C_1075]: (r2_hidden(k1_yellow_0('#skF_5', C_1075), u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5') | ~r1_yellow_0('#skF_5', C_1075) | ~r2_hidden(k1_yellow_0('#skF_5', C_1075), '#skF_6'))), inference(resolution, [status(thm)], [c_156, c_17299])).
% 19.24/10.04  tff(c_17311, plain, (![C_1075]: (r2_hidden(k1_yellow_0('#skF_5', C_1075), u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', C_1075) | ~r2_hidden(k1_yellow_0('#skF_5', C_1075), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_17072, c_17305])).
% 19.24/10.04  tff(c_17315, plain, (~r2_hidden(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_17311])).
% 19.24/10.04  tff(c_19076, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19021, c_17315])).
% 19.24/10.04  tff(c_19108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_19076])).
% 19.24/10.04  tff(c_19120, plain, (![C_1219]: (r2_hidden(k1_yellow_0('#skF_5', C_1219), u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', C_1219) | ~r2_hidden(k1_yellow_0('#skF_5', C_1219), '#skF_6'))), inference(splitRight, [status(thm)], [c_17311])).
% 19.24/10.04  tff(c_19221, plain, (![A_1221]: (r2_hidden(A_1221, u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_1221)) | ~r2_hidden(k1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_1221)), '#skF_6') | ~r2_hidden(A_1221, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_341, c_19120])).
% 19.24/10.04  tff(c_19269, plain, (![A_1222]: (r2_hidden(A_1222, u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', A_1222)) | ~r2_hidden(A_1222, '#skF_6') | ~r2_hidden(A_1222, '#skF_6') | ~r2_hidden(A_1222, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_341, c_19221])).
% 19.24/10.04  tff(c_19395, plain, (![A_1227]: (u1_struct_0('#skF_5')=A_1227 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_1227)) | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', '#skF_1'(A_1227, u1_struct_0('#skF_5')))) | ~r2_hidden('#skF_1'(A_1227, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_19269, c_4])).
% 19.24/10.04  tff(c_19398, plain, (![A_1227]: (u1_struct_0('#skF_5')=A_1227 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_1227)) | ~r2_hidden('#skF_1'(A_1227, u1_struct_0('#skF_5')), '#skF_6') | ~m1_subset_1('#skF_1'(A_1227, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_19395])).
% 19.24/10.04  tff(c_19401, plain, (![A_1227]: (u1_struct_0('#skF_5')=A_1227 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_1227)) | ~r2_hidden('#skF_1'(A_1227, u1_struct_0('#skF_5')), '#skF_6') | ~m1_subset_1('#skF_1'(A_1227, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_19398])).
% 19.24/10.04  tff(c_19403, plain, (![A_1228]: (u1_struct_0('#skF_5')=A_1228 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_1228)) | ~r2_hidden('#skF_1'(A_1228, u1_struct_0('#skF_5')), '#skF_6') | ~m1_subset_1('#skF_1'(A_1228, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_19401])).
% 19.24/10.04  tff(c_19416, plain, (![A_1229]: (u1_struct_0('#skF_5')=A_1229 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_1229)) | ~r2_hidden('#skF_1'(A_1229, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_170, c_19403])).
% 19.24/10.04  tff(c_19419, plain, (![A_1229]: (u1_struct_0('#skF_5')=A_1229 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_1229)) | v1_xboole_0('#skF_6') | ~m1_subset_1('#skF_1'(A_1229, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_12, c_19416])).
% 19.24/10.04  tff(c_19423, plain, (![A_1230]: (u1_struct_0('#skF_5')=A_1230 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_1230)) | ~m1_subset_1('#skF_1'(A_1230, u1_struct_0('#skF_5')), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_19419])).
% 19.24/10.04  tff(c_19428, plain, (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_6, c_19423])).
% 19.24/10.04  tff(c_19429, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_19428])).
% 19.24/10.04  tff(c_23265, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_23185, c_19429])).
% 19.24/10.04  tff(c_23307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_23265])).
% 19.24/10.04  tff(c_23308, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_19428])).
% 19.24/10.04  tff(c_23385, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_23308, c_245])).
% 19.24/10.04  tff(c_23393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_23385])).
% 19.24/10.04  tff(c_23395, plain, (~v13_waybel_0(u1_struct_0('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_17071])).
% 19.24/10.04  tff(c_26070, plain, (~v13_waybel_0('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_25981, c_23395])).
% 19.24/10.04  tff(c_26091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_26070])).
% 19.24/10.04  tff(c_26099, plain, (![A_1610]: (u1_struct_0('#skF_5')=A_1610 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_1610)) | ~r2_hidden('#skF_1'(A_1610, u1_struct_0('#skF_5')), '#skF_6'))), inference(splitRight, [status(thm)], [c_238])).
% 19.24/10.04  tff(c_26102, plain, (![A_1610]: (u1_struct_0('#skF_5')=A_1610 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_1610)) | v1_xboole_0('#skF_6') | ~m1_subset_1('#skF_1'(A_1610, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_12, c_26099])).
% 19.24/10.04  tff(c_26106, plain, (![A_1611]: (u1_struct_0('#skF_5')=A_1611 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_1611)) | ~m1_subset_1('#skF_1'(A_1611, u1_struct_0('#skF_5')), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_26102])).
% 19.24/10.04  tff(c_26111, plain, (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_6, c_26106])).
% 19.24/10.04  tff(c_26112, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_26111])).
% 19.24/10.04  tff(c_29825, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_29750, c_26112])).
% 19.24/10.04  tff(c_29837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_29825])).
% 19.24/10.04  tff(c_29838, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_26111])).
% 19.24/10.04  tff(c_141, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_66])).
% 19.24/10.04  tff(c_29845, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_29838, c_141])).
% 19.24/10.04  tff(c_29848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_29845])).
% 19.24/10.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.24/10.04  
% 19.24/10.04  Inference rules
% 19.24/10.04  ----------------------
% 19.24/10.04  #Ref     : 0
% 19.24/10.04  #Sup     : 5584
% 19.24/10.04  #Fact    : 0
% 19.24/10.04  #Define  : 0
% 19.24/10.04  #Split   : 45
% 19.24/10.04  #Chain   : 0
% 19.24/10.04  #Close   : 0
% 19.24/10.04  
% 19.24/10.04  Ordering : KBO
% 19.24/10.04  
% 19.24/10.04  Simplification rules
% 19.24/10.04  ----------------------
% 19.24/10.04  #Subsume      : 1836
% 19.24/10.04  #Demod        : 15792
% 19.24/10.04  #Tautology    : 1601
% 19.24/10.04  #SimpNegUnit  : 1911
% 19.24/10.04  #BackRed      : 894
% 19.24/10.04  
% 19.24/10.04  #Partial instantiations: 0
% 19.24/10.04  #Strategies tried      : 1
% 19.24/10.04  
% 19.24/10.04  Timing (in seconds)
% 19.24/10.04  ----------------------
% 19.24/10.04  Preprocessing        : 0.56
% 19.24/10.04  Parsing              : 0.29
% 19.24/10.05  CNF conversion       : 0.04
% 19.24/10.05  Main loop            : 8.59
% 19.24/10.05  Inferencing          : 2.35
% 19.24/10.05  Reduction            : 3.26
% 19.24/10.05  Demodulation         : 2.43
% 19.24/10.05  BG Simplification    : 0.25
% 19.24/10.05  Subsumption          : 2.30
% 19.24/10.05  Abstraction          : 0.40
% 19.24/10.05  MUC search           : 0.00
% 19.24/10.05  Cooper               : 0.00
% 19.24/10.05  Total                : 9.26
% 19.24/10.05  Index Insertion      : 0.00
% 19.24/10.05  Index Deletion       : 0.00
% 19.24/10.05  Index Matching       : 0.00
% 19.24/10.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
