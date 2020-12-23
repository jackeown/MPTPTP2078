%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:49 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 349 expanded)
%              Number of leaves         :   23 ( 140 expanded)
%              Depth                    :   15
%              Number of atoms          :  223 (1820 expanded)
%              Number of equality atoms :   32 ( 351 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ~ ( B != k1_xboole_0
                  & m1_orders_2(B,A,B) )
              & ~ ( ~ m1_orders_2(B,A,B)
                  & B = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( B != k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> ? [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                        & r2_hidden(D,B)
                        & C = k3_orders_2(A,B,D) ) ) )
                & ( B = k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> C = k1_xboole_0 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r2_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_orders_2)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_40,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_41,plain,(
    ~ m1_orders_2('#skF_3','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_30,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_28,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_26,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_24,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,
    ( m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_42,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_34])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_orders_2(k1_xboole_0,A_1,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    ! [A_46] :
      ( m1_orders_2('#skF_3',A_46,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_orders_2(A_46)
      | ~ v5_orders_2(A_46)
      | ~ v4_orders_2(A_46)
      | ~ v3_orders_2(A_46)
      | v2_struct_0(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_42,c_2])).

tff(c_51,plain,
    ( m1_orders_2('#skF_3','#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_48])).

tff(c_54,plain,
    ( m1_orders_2('#skF_3','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_51])).

tff(c_56,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_41,c_54])).

tff(c_57,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_58,plain,(
    m1_orders_2('#skF_3','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_12,plain,(
    ! [A_1,B_13,C_19] :
      ( m1_subset_1('#skF_1'(A_1,B_13,C_19),u1_struct_0(A_1))
      | ~ m1_orders_2(C_19,A_1,B_13)
      | k1_xboole_0 = B_13
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_88,plain,(
    ! [A_68,B_69,C_70] :
      ( k3_orders_2(A_68,B_69,'#skF_1'(A_68,B_69,C_70)) = C_70
      | ~ m1_orders_2(C_70,A_68,B_69)
      | k1_xboole_0 = B_69
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_orders_2(A_68)
      | ~ v5_orders_2(A_68)
      | ~ v4_orders_2(A_68)
      | ~ v3_orders_2(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_90,plain,(
    ! [B_69] :
      ( k3_orders_2('#skF_2',B_69,'#skF_1'('#skF_2',B_69,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_69)
      | k1_xboole_0 = B_69
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_88])).

tff(c_93,plain,(
    ! [B_69] :
      ( k3_orders_2('#skF_2',B_69,'#skF_1'('#skF_2',B_69,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_69)
      | k1_xboole_0 = B_69
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_90])).

tff(c_102,plain,(
    ! [B_75] :
      ( k3_orders_2('#skF_2',B_75,'#skF_1'('#skF_2',B_75,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_75)
      | k1_xboole_0 = B_75
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_93])).

tff(c_104,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_3')) = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_22,c_102])).

tff(c_107,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_104])).

tff(c_108,plain,(
    k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_107])).

tff(c_20,plain,(
    ! [A_30,B_38,C_42,D_44] :
      ( r2_orders_2(A_30,B_38,C_42)
      | ~ r2_hidden(B_38,k3_orders_2(A_30,D_44,C_42))
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(C_42,u1_struct_0(A_30))
      | ~ m1_subset_1(B_38,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30)
      | ~ v5_orders_2(A_30)
      | ~ v4_orders_2(A_30)
      | ~ v3_orders_2(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_111,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_20])).

tff(c_117,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_111])).

tff(c_118,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_117])).

tff(c_139,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_142,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_139])).

tff(c_145,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_58,c_142])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_57,c_145])).

tff(c_149,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_72,plain,(
    ! [A_57,B_58,C_59] :
      ( r2_hidden('#skF_1'(A_57,B_58,C_59),B_58)
      | ~ m1_orders_2(C_59,A_57,B_58)
      | k1_xboole_0 = B_58
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_orders_2(A_57)
      | ~ v5_orders_2(A_57)
      | ~ v4_orders_2(A_57)
      | ~ v3_orders_2(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,(
    ! [B_58] :
      ( r2_hidden('#skF_1'('#skF_2',B_58,'#skF_3'),B_58)
      | ~ m1_orders_2('#skF_3','#skF_2',B_58)
      | k1_xboole_0 = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_77,plain,(
    ! [B_58] :
      ( r2_hidden('#skF_1'('#skF_2',B_58,'#skF_3'),B_58)
      | ~ m1_orders_2('#skF_3','#skF_2',B_58)
      | k1_xboole_0 = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_74])).

tff(c_79,plain,(
    ! [B_60] :
      ( r2_hidden('#skF_1'('#skF_2',B_60,'#skF_3'),B_60)
      | ~ m1_orders_2('#skF_3','#skF_2',B_60)
      | k1_xboole_0 = B_60
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_77])).

tff(c_81,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_22,c_79])).

tff(c_84,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_81])).

tff(c_85,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_84])).

tff(c_148,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_150,plain,(
    ! [B_78] :
      ( r2_orders_2('#skF_2',B_78,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_78,'#skF_3')
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_14,plain,(
    ! [A_23,C_29,B_27] :
      ( ~ r2_orders_2(A_23,C_29,B_27)
      | ~ r2_orders_2(A_23,B_27,C_29)
      | ~ m1_subset_1(C_29,u1_struct_0(A_23))
      | ~ m1_subset_1(B_27,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v5_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_152,plain,(
    ! [B_78] :
      ( ~ r2_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_3'),B_78)
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ r2_hidden(B_78,'#skF_3')
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_150,c_14])).

tff(c_156,plain,(
    ! [B_79] :
      ( ~ r2_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_3'),B_79)
      | ~ r2_hidden(B_79,'#skF_3')
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_149,c_152])).

tff(c_160,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_148,c_156])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_85,c_160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.22  
% 2.32/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.23  %$ r2_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.32/1.23  
% 2.32/1.23  %Foreground sorts:
% 2.32/1.23  
% 2.32/1.23  
% 2.32/1.23  %Background operators:
% 2.32/1.23  
% 2.32/1.23  
% 2.32/1.23  %Foreground operators:
% 2.32/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.32/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.32/1.23  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.32/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.23  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.32/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.23  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.32/1.23  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.32/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.23  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.32/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.23  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.32/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.23  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.32/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.32/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.23  
% 2.46/1.24  tff(f_128, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k1_xboole_0) & m1_orders_2(B, A, B)) & ~(~m1_orders_2(B, A, B) & (B = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_orders_2)).
% 2.46/1.24  tff(f_60, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_orders_2)).
% 2.46/1.24  tff(f_101, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 2.46/1.24  tff(f_75, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_orders_2)).
% 2.46/1.24  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.46/1.24  tff(c_40, plain, (k1_xboole_0!='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.46/1.24  tff(c_41, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 2.46/1.24  tff(c_30, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.46/1.24  tff(c_28, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.46/1.24  tff(c_26, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.46/1.24  tff(c_24, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.46/1.24  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.46/1.24  tff(c_34, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.46/1.24  tff(c_42, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_41, c_34])).
% 2.46/1.24  tff(c_2, plain, (![A_1]: (m1_orders_2(k1_xboole_0, A_1, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1) | ~v4_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.46/1.24  tff(c_48, plain, (![A_46]: (m1_orders_2('#skF_3', A_46, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_orders_2(A_46) | ~v5_orders_2(A_46) | ~v4_orders_2(A_46) | ~v3_orders_2(A_46) | v2_struct_0(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_42, c_2])).
% 2.46/1.24  tff(c_51, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3') | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_48])).
% 2.46/1.24  tff(c_54, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_51])).
% 2.46/1.24  tff(c_56, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_41, c_54])).
% 2.46/1.24  tff(c_57, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_40])).
% 2.46/1.24  tff(c_58, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 2.46/1.24  tff(c_12, plain, (![A_1, B_13, C_19]: (m1_subset_1('#skF_1'(A_1, B_13, C_19), u1_struct_0(A_1)) | ~m1_orders_2(C_19, A_1, B_13) | k1_xboole_0=B_13 | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1) | ~v4_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.46/1.24  tff(c_88, plain, (![A_68, B_69, C_70]: (k3_orders_2(A_68, B_69, '#skF_1'(A_68, B_69, C_70))=C_70 | ~m1_orders_2(C_70, A_68, B_69) | k1_xboole_0=B_69 | ~m1_subset_1(C_70, k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_orders_2(A_68) | ~v5_orders_2(A_68) | ~v4_orders_2(A_68) | ~v3_orders_2(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.46/1.24  tff(c_90, plain, (![B_69]: (k3_orders_2('#skF_2', B_69, '#skF_1'('#skF_2', B_69, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_69) | k1_xboole_0=B_69 | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_88])).
% 2.46/1.24  tff(c_93, plain, (![B_69]: (k3_orders_2('#skF_2', B_69, '#skF_1'('#skF_2', B_69, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_69) | k1_xboole_0=B_69 | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_90])).
% 2.46/1.24  tff(c_102, plain, (![B_75]: (k3_orders_2('#skF_2', B_75, '#skF_1'('#skF_2', B_75, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_75) | k1_xboole_0=B_75 | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_32, c_93])).
% 2.46/1.24  tff(c_104, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_22, c_102])).
% 2.46/1.24  tff(c_107, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_104])).
% 2.46/1.24  tff(c_108, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_57, c_107])).
% 2.46/1.24  tff(c_20, plain, (![A_30, B_38, C_42, D_44]: (r2_orders_2(A_30, B_38, C_42) | ~r2_hidden(B_38, k3_orders_2(A_30, D_44, C_42)) | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(C_42, u1_struct_0(A_30)) | ~m1_subset_1(B_38, u1_struct_0(A_30)) | ~l1_orders_2(A_30) | ~v5_orders_2(A_30) | ~v4_orders_2(A_30) | ~v3_orders_2(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.46/1.24  tff(c_111, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_108, c_20])).
% 2.46/1.24  tff(c_117, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_111])).
% 2.46/1.24  tff(c_118, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_117])).
% 2.46/1.24  tff(c_139, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_118])).
% 2.46/1.24  tff(c_142, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_139])).
% 2.46/1.24  tff(c_145, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_58, c_142])).
% 2.46/1.24  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_57, c_145])).
% 2.46/1.24  tff(c_149, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_118])).
% 2.46/1.24  tff(c_72, plain, (![A_57, B_58, C_59]: (r2_hidden('#skF_1'(A_57, B_58, C_59), B_58) | ~m1_orders_2(C_59, A_57, B_58) | k1_xboole_0=B_58 | ~m1_subset_1(C_59, k1_zfmisc_1(u1_struct_0(A_57))) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_orders_2(A_57) | ~v5_orders_2(A_57) | ~v4_orders_2(A_57) | ~v3_orders_2(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.46/1.24  tff(c_74, plain, (![B_58]: (r2_hidden('#skF_1'('#skF_2', B_58, '#skF_3'), B_58) | ~m1_orders_2('#skF_3', '#skF_2', B_58) | k1_xboole_0=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_72])).
% 2.46/1.24  tff(c_77, plain, (![B_58]: (r2_hidden('#skF_1'('#skF_2', B_58, '#skF_3'), B_58) | ~m1_orders_2('#skF_3', '#skF_2', B_58) | k1_xboole_0=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_74])).
% 2.46/1.24  tff(c_79, plain, (![B_60]: (r2_hidden('#skF_1'('#skF_2', B_60, '#skF_3'), B_60) | ~m1_orders_2('#skF_3', '#skF_2', B_60) | k1_xboole_0=B_60 | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_32, c_77])).
% 2.46/1.24  tff(c_81, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | ~m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_22, c_79])).
% 2.46/1.24  tff(c_84, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_81])).
% 2.46/1.24  tff(c_85, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_57, c_84])).
% 2.46/1.24  tff(c_148, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_118])).
% 2.46/1.24  tff(c_150, plain, (![B_78]: (r2_orders_2('#skF_2', B_78, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_78, '#skF_3') | ~m1_subset_1(B_78, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_118])).
% 2.46/1.24  tff(c_14, plain, (![A_23, C_29, B_27]: (~r2_orders_2(A_23, C_29, B_27) | ~r2_orders_2(A_23, B_27, C_29) | ~m1_subset_1(C_29, u1_struct_0(A_23)) | ~m1_subset_1(B_27, u1_struct_0(A_23)) | ~l1_orders_2(A_23) | ~v5_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.46/1.24  tff(c_152, plain, (![B_78]: (~r2_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', '#skF_3'), B_78) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~r2_hidden(B_78, '#skF_3') | ~m1_subset_1(B_78, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_150, c_14])).
% 2.46/1.24  tff(c_156, plain, (![B_79]: (~r2_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', '#skF_3'), B_79) | ~r2_hidden(B_79, '#skF_3') | ~m1_subset_1(B_79, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_149, c_152])).
% 2.46/1.24  tff(c_160, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_148, c_156])).
% 2.46/1.24  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_85, c_160])).
% 2.46/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.24  
% 2.46/1.24  Inference rules
% 2.46/1.24  ----------------------
% 2.46/1.24  #Ref     : 0
% 2.46/1.24  #Sup     : 19
% 2.46/1.24  #Fact    : 0
% 2.46/1.24  #Define  : 0
% 2.46/1.24  #Split   : 3
% 2.46/1.24  #Chain   : 0
% 2.46/1.24  #Close   : 0
% 2.46/1.24  
% 2.46/1.24  Ordering : KBO
% 2.46/1.24  
% 2.46/1.24  Simplification rules
% 2.46/1.24  ----------------------
% 2.46/1.24  #Subsume      : 0
% 2.46/1.24  #Demod        : 57
% 2.46/1.24  #Tautology    : 11
% 2.46/1.24  #SimpNegUnit  : 14
% 2.46/1.24  #BackRed      : 0
% 2.46/1.24  
% 2.46/1.24  #Partial instantiations: 0
% 2.46/1.24  #Strategies tried      : 1
% 2.46/1.24  
% 2.46/1.24  Timing (in seconds)
% 2.46/1.24  ----------------------
% 2.46/1.25  Preprocessing        : 0.31
% 2.46/1.25  Parsing              : 0.16
% 2.46/1.25  CNF conversion       : 0.03
% 2.46/1.25  Main loop            : 0.17
% 2.46/1.25  Inferencing          : 0.06
% 2.46/1.25  Reduction            : 0.05
% 2.46/1.25  Demodulation         : 0.03
% 2.46/1.25  BG Simplification    : 0.01
% 2.46/1.25  Subsumption          : 0.03
% 2.46/1.25  Abstraction          : 0.01
% 2.46/1.25  MUC search           : 0.00
% 2.46/1.25  Cooper               : 0.00
% 2.46/1.25  Total                : 0.52
% 2.46/1.25  Index Insertion      : 0.00
% 2.46/1.25  Index Deletion       : 0.00
% 2.46/1.25  Index Matching       : 0.00
% 2.46/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
