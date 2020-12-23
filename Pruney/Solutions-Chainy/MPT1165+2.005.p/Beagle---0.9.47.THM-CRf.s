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
% DateTime   : Thu Dec  3 10:19:49 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 153 expanded)
%              Number of leaves         :   21 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  178 ( 720 expanded)
%              Number of equality atoms :   32 ( 147 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ r2_hidden(B,k3_orders_2(A,C,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_orders_2)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_34,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_35,plain,(
    ~ m1_orders_2('#skF_3','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_24,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_22,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_20,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_18,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_28,plain,
    ( m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_36,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_28])).

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

tff(c_42,plain,(
    ! [A_31] :
      ( m1_orders_2('#skF_3',A_31,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_orders_2(A_31)
      | ~ v5_orders_2(A_31)
      | ~ v4_orders_2(A_31)
      | ~ v3_orders_2(A_31)
      | v2_struct_0(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_36,c_2])).

tff(c_45,plain,
    ( m1_orders_2('#skF_3','#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_42])).

tff(c_48,plain,
    ( m1_orders_2('#skF_3','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_18,c_45])).

tff(c_50,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_35,c_48])).

tff(c_51,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_52,plain,(
    m1_orders_2('#skF_3','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

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

tff(c_65,plain,(
    ! [A_38,B_39,C_40] :
      ( r2_hidden('#skF_1'(A_38,B_39,C_40),B_39)
      | ~ m1_orders_2(C_40,A_38,B_39)
      | k1_xboole_0 = B_39
      | ~ m1_subset_1(C_40,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_orders_2(A_38)
      | ~ v5_orders_2(A_38)
      | ~ v4_orders_2(A_38)
      | ~ v3_orders_2(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_67,plain,(
    ! [B_39] :
      ( r2_hidden('#skF_1'('#skF_2',B_39,'#skF_3'),B_39)
      | ~ m1_orders_2('#skF_3','#skF_2',B_39)
      | k1_xboole_0 = B_39
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_65])).

tff(c_70,plain,(
    ! [B_39] :
      ( r2_hidden('#skF_1'('#skF_2',B_39,'#skF_3'),B_39)
      | ~ m1_orders_2('#skF_3','#skF_2',B_39)
      | k1_xboole_0 = B_39
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_18,c_67])).

tff(c_72,plain,(
    ! [B_41] :
      ( r2_hidden('#skF_1'('#skF_2',B_41,'#skF_3'),B_41)
      | ~ m1_orders_2('#skF_3','#skF_2',B_41)
      | k1_xboole_0 = B_41
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_70])).

tff(c_74,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16,c_72])).

tff(c_77,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_74])).

tff(c_78,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_77])).

tff(c_80,plain,(
    ! [A_45,B_46,C_47] :
      ( k3_orders_2(A_45,B_46,'#skF_1'(A_45,B_46,C_47)) = C_47
      | ~ m1_orders_2(C_47,A_45,B_46)
      | k1_xboole_0 = B_46
      | ~ m1_subset_1(C_47,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_orders_2(A_45)
      | ~ v5_orders_2(A_45)
      | ~ v4_orders_2(A_45)
      | ~ v3_orders_2(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_82,plain,(
    ! [B_46] :
      ( k3_orders_2('#skF_2',B_46,'#skF_1'('#skF_2',B_46,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_46)
      | k1_xboole_0 = B_46
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_80])).

tff(c_85,plain,(
    ! [B_46] :
      ( k3_orders_2('#skF_2',B_46,'#skF_1'('#skF_2',B_46,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_46)
      | k1_xboole_0 = B_46
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_18,c_82])).

tff(c_87,plain,(
    ! [B_48] :
      ( k3_orders_2('#skF_2',B_48,'#skF_1'('#skF_2',B_48,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_48)
      | k1_xboole_0 = B_48
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_85])).

tff(c_89,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_3')) = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16,c_87])).

tff(c_92,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_89])).

tff(c_93,plain,(
    k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_92])).

tff(c_14,plain,(
    ! [B_27,A_23,C_29] :
      ( ~ r2_hidden(B_27,k3_orders_2(A_23,C_29,B_27))
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_subset_1(B_27,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_96,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_14])).

tff(c_100,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_18,c_16,c_78,c_96])).

tff(c_101,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_100])).

tff(c_111,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_101])).

tff(c_114,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_18,c_16,c_52,c_111])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_51,c_114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:20:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.21  
% 2.09/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.21  %$ m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.09/1.21  
% 2.09/1.21  %Foreground sorts:
% 2.09/1.21  
% 2.09/1.21  
% 2.09/1.21  %Background operators:
% 2.09/1.21  
% 2.09/1.21  
% 2.09/1.21  %Foreground operators:
% 2.09/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.09/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.09/1.21  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.09/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.21  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.09/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.21  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.09/1.21  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.09/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.21  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.09/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.21  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.09/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.09/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.21  
% 2.09/1.22  tff(f_107, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k1_xboole_0) & m1_orders_2(B, A, B)) & ~(~m1_orders_2(B, A, B) & (B = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_orders_2)).
% 2.09/1.22  tff(f_60, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_orders_2)).
% 2.09/1.22  tff(f_80, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~r2_hidden(B, k3_orders_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_orders_2)).
% 2.09/1.22  tff(c_26, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.09/1.22  tff(c_34, plain, (k1_xboole_0!='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.09/1.22  tff(c_35, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 2.09/1.22  tff(c_24, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.09/1.22  tff(c_22, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.09/1.22  tff(c_20, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.09/1.22  tff(c_18, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.09/1.22  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.09/1.22  tff(c_28, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.09/1.22  tff(c_36, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_35, c_28])).
% 2.09/1.22  tff(c_2, plain, (![A_1]: (m1_orders_2(k1_xboole_0, A_1, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1) | ~v4_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.09/1.22  tff(c_42, plain, (![A_31]: (m1_orders_2('#skF_3', A_31, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_orders_2(A_31) | ~v5_orders_2(A_31) | ~v4_orders_2(A_31) | ~v3_orders_2(A_31) | v2_struct_0(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_36, c_2])).
% 2.09/1.22  tff(c_45, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3') | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_16, c_42])).
% 2.09/1.22  tff(c_48, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_18, c_45])).
% 2.09/1.22  tff(c_50, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_35, c_48])).
% 2.09/1.22  tff(c_51, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 2.09/1.22  tff(c_52, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.09/1.22  tff(c_12, plain, (![A_1, B_13, C_19]: (m1_subset_1('#skF_1'(A_1, B_13, C_19), u1_struct_0(A_1)) | ~m1_orders_2(C_19, A_1, B_13) | k1_xboole_0=B_13 | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1) | ~v4_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.09/1.22  tff(c_65, plain, (![A_38, B_39, C_40]: (r2_hidden('#skF_1'(A_38, B_39, C_40), B_39) | ~m1_orders_2(C_40, A_38, B_39) | k1_xboole_0=B_39 | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_orders_2(A_38) | ~v5_orders_2(A_38) | ~v4_orders_2(A_38) | ~v3_orders_2(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.09/1.22  tff(c_67, plain, (![B_39]: (r2_hidden('#skF_1'('#skF_2', B_39, '#skF_3'), B_39) | ~m1_orders_2('#skF_3', '#skF_2', B_39) | k1_xboole_0=B_39 | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_65])).
% 2.09/1.22  tff(c_70, plain, (![B_39]: (r2_hidden('#skF_1'('#skF_2', B_39, '#skF_3'), B_39) | ~m1_orders_2('#skF_3', '#skF_2', B_39) | k1_xboole_0=B_39 | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_18, c_67])).
% 2.09/1.22  tff(c_72, plain, (![B_41]: (r2_hidden('#skF_1'('#skF_2', B_41, '#skF_3'), B_41) | ~m1_orders_2('#skF_3', '#skF_2', B_41) | k1_xboole_0=B_41 | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_26, c_70])).
% 2.09/1.22  tff(c_74, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | ~m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_16, c_72])).
% 2.09/1.22  tff(c_77, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_74])).
% 2.09/1.22  tff(c_78, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_51, c_77])).
% 2.09/1.22  tff(c_80, plain, (![A_45, B_46, C_47]: (k3_orders_2(A_45, B_46, '#skF_1'(A_45, B_46, C_47))=C_47 | ~m1_orders_2(C_47, A_45, B_46) | k1_xboole_0=B_46 | ~m1_subset_1(C_47, k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_orders_2(A_45) | ~v5_orders_2(A_45) | ~v4_orders_2(A_45) | ~v3_orders_2(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.09/1.22  tff(c_82, plain, (![B_46]: (k3_orders_2('#skF_2', B_46, '#skF_1'('#skF_2', B_46, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_46) | k1_xboole_0=B_46 | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_80])).
% 2.09/1.22  tff(c_85, plain, (![B_46]: (k3_orders_2('#skF_2', B_46, '#skF_1'('#skF_2', B_46, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_46) | k1_xboole_0=B_46 | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_18, c_82])).
% 2.09/1.22  tff(c_87, plain, (![B_48]: (k3_orders_2('#skF_2', B_48, '#skF_1'('#skF_2', B_48, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_48) | k1_xboole_0=B_48 | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_26, c_85])).
% 2.09/1.22  tff(c_89, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_16, c_87])).
% 2.09/1.22  tff(c_92, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_89])).
% 2.09/1.22  tff(c_93, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_51, c_92])).
% 2.09/1.22  tff(c_14, plain, (![B_27, A_23, C_29]: (~r2_hidden(B_27, k3_orders_2(A_23, C_29, B_27)) | ~m1_subset_1(C_29, k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_subset_1(B_27, u1_struct_0(A_23)) | ~l1_orders_2(A_23) | ~v5_orders_2(A_23) | ~v4_orders_2(A_23) | ~v3_orders_2(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.09/1.22  tff(c_96, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_93, c_14])).
% 2.09/1.22  tff(c_100, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_18, c_16, c_78, c_96])).
% 2.09/1.22  tff(c_101, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_100])).
% 2.09/1.22  tff(c_111, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_101])).
% 2.09/1.22  tff(c_114, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_18, c_16, c_52, c_111])).
% 2.09/1.22  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_51, c_114])).
% 2.09/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.22  
% 2.09/1.22  Inference rules
% 2.09/1.22  ----------------------
% 2.09/1.22  #Ref     : 0
% 2.09/1.22  #Sup     : 13
% 2.09/1.22  #Fact    : 0
% 2.09/1.22  #Define  : 0
% 2.09/1.22  #Split   : 2
% 2.09/1.22  #Chain   : 0
% 2.09/1.22  #Close   : 0
% 2.09/1.22  
% 2.09/1.22  Ordering : KBO
% 2.09/1.22  
% 2.09/1.22  Simplification rules
% 2.09/1.22  ----------------------
% 2.09/1.22  #Subsume      : 0
% 2.09/1.22  #Demod        : 43
% 2.09/1.22  #Tautology    : 8
% 2.09/1.22  #SimpNegUnit  : 11
% 2.09/1.22  #BackRed      : 0
% 2.09/1.22  
% 2.09/1.22  #Partial instantiations: 0
% 2.09/1.22  #Strategies tried      : 1
% 2.09/1.22  
% 2.09/1.22  Timing (in seconds)
% 2.09/1.22  ----------------------
% 2.09/1.23  Preprocessing        : 0.32
% 2.09/1.23  Parsing              : 0.16
% 2.09/1.23  CNF conversion       : 0.02
% 2.09/1.23  Main loop            : 0.15
% 2.09/1.23  Inferencing          : 0.05
% 2.09/1.23  Reduction            : 0.05
% 2.09/1.23  Demodulation         : 0.03
% 2.09/1.23  BG Simplification    : 0.01
% 2.09/1.23  Subsumption          : 0.03
% 2.09/1.23  Abstraction          : 0.01
% 2.09/1.23  MUC search           : 0.00
% 2.09/1.23  Cooper               : 0.00
% 2.09/1.23  Total                : 0.50
% 2.09/1.23  Index Insertion      : 0.00
% 2.09/1.23  Index Deletion       : 0.00
% 2.09/1.23  Index Matching       : 0.00
% 2.09/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
