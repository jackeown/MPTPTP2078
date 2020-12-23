%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1627+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:08 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   55 (  93 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :  161 ( 502 expanded)
%              Number of equality atoms :   27 (  78 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_yellow_0 > v4_waybel_0 > v1_waybel_0 > r2_hidden > r1_yellow_0 > m1_yellow_0 > m1_subset_1 > v4_orders_2 > v2_struct_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v4_waybel_0,type,(
    v4_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v4_yellow_0,type,(
    v4_yellow_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(v1_waybel_0,type,(
    v1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_yellow_0(B,A)
              & v4_waybel_0(B,A)
              & m1_yellow_0(B,A) )
           => ! [C] :
                ( ( v1_waybel_0(C,B)
                  & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
               => ( r1_yellow_0(A,C)
                 => ( C = k1_xboole_0
                    | ( r1_yellow_0(B,C)
                      & k1_yellow_0(B,C) = k1_yellow_0(A,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_waybel_0)).

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_yellow_0(B,A)
         => ( v4_waybel_0(B,A)
          <=> ! [C] :
                ( ( v1_waybel_0(C,B)
                  & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
               => ( r1_yellow_0(A,C)
                 => ( C = k1_xboole_0
                    | r2_hidden(k1_yellow_0(A,C),u1_struct_0(B)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_waybel_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_yellow_0(B,A)
            & m1_yellow_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( ( r1_yellow_0(A,C)
                  & r2_hidden(k1_yellow_0(A,C),u1_struct_0(B)) )
               => ( r1_yellow_0(B,C)
                  & k1_yellow_0(B,C) = k1_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_yellow_0)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_18,plain,
    ( k1_yellow_0('#skF_2','#skF_4') != k1_yellow_0('#skF_3','#skF_4')
    | ~ r1_yellow_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_41,plain,(
    ~ r1_yellow_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_26,plain,(
    v1_waybel_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_22,plain,(
    r1_yellow_0('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    m1_yellow_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    v4_waybel_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_38,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    v4_yellow_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    ! [A_1,C_10,B_7] :
      ( r2_hidden(k1_yellow_0(A_1,C_10),u1_struct_0(B_7))
      | k1_xboole_0 = C_10
      | ~ r1_yellow_0(A_1,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(u1_struct_0(B_7)))
      | ~ v1_waybel_0(C_10,B_7)
      | ~ v4_waybel_0(B_7,A_1)
      | ~ m1_yellow_0(B_7,A_1)
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,(
    ! [B_35,C_36,A_37] :
      ( r1_yellow_0(B_35,C_36)
      | ~ r2_hidden(k1_yellow_0(A_37,C_36),u1_struct_0(B_35))
      | ~ r1_yellow_0(A_37,C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0(B_35)))
      | ~ m1_yellow_0(B_35,A_37)
      | ~ v4_yellow_0(B_35,A_37)
      | v2_struct_0(B_35)
      | ~ l1_orders_2(A_37)
      | ~ v4_orders_2(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_58,plain,(
    ! [B_38,C_39,A_40] :
      ( r1_yellow_0(B_38,C_39)
      | ~ v4_yellow_0(B_38,A_40)
      | v2_struct_0(B_38)
      | ~ v4_orders_2(A_40)
      | k1_xboole_0 = C_39
      | ~ r1_yellow_0(A_40,C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(B_38)))
      | ~ v1_waybel_0(C_39,B_38)
      | ~ v4_waybel_0(B_38,A_40)
      | ~ m1_yellow_0(B_38,A_40)
      | ~ l1_orders_2(A_40)
      | v2_struct_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_2,c_53])).

tff(c_60,plain,(
    ! [C_39] :
      ( r1_yellow_0('#skF_3',C_39)
      | v2_struct_0('#skF_3')
      | ~ v4_orders_2('#skF_2')
      | k1_xboole_0 = C_39
      | ~ r1_yellow_0('#skF_2',C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_waybel_0(C_39,'#skF_3')
      | ~ v4_waybel_0('#skF_3','#skF_2')
      | ~ m1_yellow_0('#skF_3','#skF_2')
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_63,plain,(
    ! [C_39] :
      ( r1_yellow_0('#skF_3',C_39)
      | v2_struct_0('#skF_3')
      | k1_xboole_0 = C_39
      | ~ r1_yellow_0('#skF_2',C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_waybel_0(C_39,'#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_30,c_38,c_60])).

tff(c_65,plain,(
    ! [C_41] :
      ( r1_yellow_0('#skF_3',C_41)
      | k1_xboole_0 = C_41
      | ~ r1_yellow_0('#skF_2',C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_waybel_0(C_41,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_34,c_63])).

tff(c_72,plain,
    ( r1_yellow_0('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ r1_yellow_0('#skF_2','#skF_4')
    | ~ v1_waybel_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_65])).

tff(c_76,plain,
    ( r1_yellow_0('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_72])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_41,c_76])).

tff(c_79,plain,(
    k1_yellow_0('#skF_2','#skF_4') != k1_yellow_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_132,plain,(
    ! [B_64,C_65,A_66] :
      ( k1_yellow_0(B_64,C_65) = k1_yellow_0(A_66,C_65)
      | ~ r2_hidden(k1_yellow_0(A_66,C_65),u1_struct_0(B_64))
      | ~ r1_yellow_0(A_66,C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0(B_64)))
      | ~ m1_yellow_0(B_64,A_66)
      | ~ v4_yellow_0(B_64,A_66)
      | v2_struct_0(B_64)
      | ~ l1_orders_2(A_66)
      | ~ v4_orders_2(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_137,plain,(
    ! [B_67,C_68,A_69] :
      ( k1_yellow_0(B_67,C_68) = k1_yellow_0(A_69,C_68)
      | ~ v4_yellow_0(B_67,A_69)
      | v2_struct_0(B_67)
      | ~ v4_orders_2(A_69)
      | k1_xboole_0 = C_68
      | ~ r1_yellow_0(A_69,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(B_67)))
      | ~ v1_waybel_0(C_68,B_67)
      | ~ v4_waybel_0(B_67,A_69)
      | ~ m1_yellow_0(B_67,A_69)
      | ~ l1_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_2,c_132])).

tff(c_139,plain,(
    ! [C_68] :
      ( k1_yellow_0('#skF_2',C_68) = k1_yellow_0('#skF_3',C_68)
      | v2_struct_0('#skF_3')
      | ~ v4_orders_2('#skF_2')
      | k1_xboole_0 = C_68
      | ~ r1_yellow_0('#skF_2',C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_waybel_0(C_68,'#skF_3')
      | ~ v4_waybel_0('#skF_3','#skF_2')
      | ~ m1_yellow_0('#skF_3','#skF_2')
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_137])).

tff(c_142,plain,(
    ! [C_68] :
      ( k1_yellow_0('#skF_2',C_68) = k1_yellow_0('#skF_3',C_68)
      | v2_struct_0('#skF_3')
      | k1_xboole_0 = C_68
      | ~ r1_yellow_0('#skF_2',C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_waybel_0(C_68,'#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_30,c_38,c_139])).

tff(c_144,plain,(
    ! [C_70] :
      ( k1_yellow_0('#skF_2',C_70) = k1_yellow_0('#skF_3',C_70)
      | k1_xboole_0 = C_70
      | ~ r1_yellow_0('#skF_2',C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_waybel_0(C_70,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_34,c_142])).

tff(c_151,plain,
    ( k1_yellow_0('#skF_2','#skF_4') = k1_yellow_0('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ r1_yellow_0('#skF_2','#skF_4')
    | ~ v1_waybel_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_144])).

tff(c_155,plain,
    ( k1_yellow_0('#skF_2','#skF_4') = k1_yellow_0('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_151])).

tff(c_157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_79,c_155])).

%------------------------------------------------------------------------------
