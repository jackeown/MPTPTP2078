%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:49 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 300 expanded)
%              Number of leaves         :   23 ( 122 expanded)
%              Depth                    :   14
%              Number of atoms          :  210 (1538 expanded)
%              Number of equality atoms :   32 ( 299 expanded)
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

tff(f_146,negated_conjecture,(
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

tff(f_66,axiom,(
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

tff(f_119,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ~ r2_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_44,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_45,plain,(
    ~ m1_orders_2('#skF_3','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_34,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_32,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_30,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_28,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_38,plain,
    ( m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_46,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_38])).

tff(c_4,plain,(
    ! [A_4] :
      ( m1_orders_2(k1_xboole_0,A_4,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_orders_2(A_4)
      | ~ v5_orders_2(A_4)
      | ~ v4_orders_2(A_4)
      | ~ v3_orders_2(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_58,plain,(
    ! [A_56] :
      ( m1_orders_2('#skF_3',A_56,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_orders_2(A_56)
      | ~ v5_orders_2(A_56)
      | ~ v4_orders_2(A_56)
      | ~ v3_orders_2(A_56)
      | v2_struct_0(A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_46,c_4])).

tff(c_61,plain,
    ( m1_orders_2('#skF_3','#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_58])).

tff(c_64,plain,
    ( m1_orders_2('#skF_3','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_61])).

tff(c_66,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_45,c_64])).

tff(c_67,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_68,plain,(
    m1_orders_2('#skF_3','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_14,plain,(
    ! [A_4,B_16,C_22] :
      ( m1_subset_1('#skF_1'(A_4,B_16,C_22),u1_struct_0(A_4))
      | ~ m1_orders_2(C_22,A_4,B_16)
      | k1_xboole_0 = B_16
      | ~ m1_subset_1(C_22,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_orders_2(A_4)
      | ~ v5_orders_2(A_4)
      | ~ v4_orders_2(A_4)
      | ~ v3_orders_2(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_110,plain,(
    ! [A_85,B_86,C_87] :
      ( k3_orders_2(A_85,B_86,'#skF_1'(A_85,B_86,C_87)) = C_87
      | ~ m1_orders_2(C_87,A_85,B_86)
      | k1_xboole_0 = B_86
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85)
      | ~ v5_orders_2(A_85)
      | ~ v4_orders_2(A_85)
      | ~ v3_orders_2(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_112,plain,(
    ! [B_86] :
      ( k3_orders_2('#skF_2',B_86,'#skF_1'('#skF_2',B_86,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_86)
      | k1_xboole_0 = B_86
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_110])).

tff(c_115,plain,(
    ! [B_86] :
      ( k3_orders_2('#skF_2',B_86,'#skF_1'('#skF_2',B_86,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_86)
      | k1_xboole_0 = B_86
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_112])).

tff(c_117,plain,(
    ! [B_88] :
      ( k3_orders_2('#skF_2',B_88,'#skF_1'('#skF_2',B_88,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_88)
      | k1_xboole_0 = B_88
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_115])).

tff(c_119,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_3')) = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_117])).

tff(c_122,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_119])).

tff(c_123,plain,(
    k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_122])).

tff(c_24,plain,(
    ! [A_33,B_41,C_45,D_47] :
      ( r2_orders_2(A_33,B_41,C_45)
      | ~ r2_hidden(B_41,k3_orders_2(A_33,D_47,C_45))
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(C_45,u1_struct_0(A_33))
      | ~ m1_subset_1(B_41,u1_struct_0(A_33))
      | ~ l1_orders_2(A_33)
      | ~ v5_orders_2(A_33)
      | ~ v4_orders_2(A_33)
      | ~ v3_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_126,plain,(
    ! [B_41] :
      ( r2_orders_2('#skF_2',B_41,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_41,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_24])).

tff(c_132,plain,(
    ! [B_41] :
      ( r2_orders_2('#skF_2',B_41,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_41,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_126])).

tff(c_133,plain,(
    ! [B_41] :
      ( r2_orders_2('#skF_2',B_41,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_41,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_132])).

tff(c_138,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_141,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_138])).

tff(c_147,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_68,c_141])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_67,c_147])).

tff(c_151,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_93,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden('#skF_1'(A_70,B_71,C_72),B_71)
      | ~ m1_orders_2(C_72,A_70,B_71)
      | k1_xboole_0 = B_71
      | ~ m1_subset_1(C_72,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_orders_2(A_70)
      | ~ v5_orders_2(A_70)
      | ~ v4_orders_2(A_70)
      | ~ v3_orders_2(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_95,plain,(
    ! [B_71] :
      ( r2_hidden('#skF_1'('#skF_2',B_71,'#skF_3'),B_71)
      | ~ m1_orders_2('#skF_3','#skF_2',B_71)
      | k1_xboole_0 = B_71
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_93])).

tff(c_98,plain,(
    ! [B_71] :
      ( r2_hidden('#skF_1'('#skF_2',B_71,'#skF_3'),B_71)
      | ~ m1_orders_2('#skF_3','#skF_2',B_71)
      | k1_xboole_0 = B_71
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_95])).

tff(c_101,plain,(
    ! [B_77] :
      ( r2_hidden('#skF_1'('#skF_2',B_77,'#skF_3'),B_77)
      | ~ m1_orders_2('#skF_3','#skF_2',B_77)
      | k1_xboole_0 = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_98])).

tff(c_103,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_101])).

tff(c_106,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_103])).

tff(c_107,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_106])).

tff(c_159,plain,(
    ! [B_93] :
      ( r2_orders_2('#skF_2',B_93,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_93,'#skF_3')
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_18,plain,(
    ! [A_30,B_31,C_32] :
      ( ~ r2_orders_2(A_30,B_31,B_31)
      | ~ m1_subset_1(C_32,u1_struct_0(A_30))
      | ~ m1_subset_1(B_31,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_162,plain,(
    ! [C_32] :
      ( ~ m1_subset_1(C_32,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_159,c_18])).

tff(c_165,plain,(
    ! [C_32] : ~ m1_subset_1(C_32,u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_107,c_28,c_162])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.36  
% 2.30/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.36  %$ r2_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.30/1.36  
% 2.30/1.36  %Foreground sorts:
% 2.30/1.36  
% 2.30/1.36  
% 2.30/1.36  %Background operators:
% 2.30/1.36  
% 2.30/1.36  
% 2.30/1.36  %Foreground operators:
% 2.30/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.30/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.30/1.36  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.30/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.36  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.30/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.36  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.30/1.36  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.30/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.36  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.30/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.36  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.30/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.36  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.30/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.30/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.36  
% 2.50/1.38  tff(f_146, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k1_xboole_0) & m1_orders_2(B, A, B)) & ~(~m1_orders_2(B, A, B) & (B = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_orders_2)).
% 2.50/1.38  tff(f_66, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_orders_2)).
% 2.50/1.38  tff(f_119, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 2.50/1.38  tff(f_93, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => ~r2_orders_2(A, B, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_orders_2)).
% 2.50/1.38  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.50/1.38  tff(c_44, plain, (k1_xboole_0!='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.50/1.38  tff(c_45, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 2.50/1.38  tff(c_34, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.50/1.38  tff(c_32, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.50/1.38  tff(c_30, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.50/1.38  tff(c_28, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.50/1.38  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.50/1.38  tff(c_38, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.50/1.38  tff(c_46, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_45, c_38])).
% 2.50/1.38  tff(c_4, plain, (![A_4]: (m1_orders_2(k1_xboole_0, A_4, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_orders_2(A_4) | ~v5_orders_2(A_4) | ~v4_orders_2(A_4) | ~v3_orders_2(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.50/1.38  tff(c_58, plain, (![A_56]: (m1_orders_2('#skF_3', A_56, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_orders_2(A_56) | ~v5_orders_2(A_56) | ~v4_orders_2(A_56) | ~v3_orders_2(A_56) | v2_struct_0(A_56))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_46, c_4])).
% 2.50/1.38  tff(c_61, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3') | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_58])).
% 2.50/1.38  tff(c_64, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_61])).
% 2.50/1.38  tff(c_66, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_45, c_64])).
% 2.50/1.38  tff(c_67, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 2.50/1.38  tff(c_68, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 2.50/1.38  tff(c_14, plain, (![A_4, B_16, C_22]: (m1_subset_1('#skF_1'(A_4, B_16, C_22), u1_struct_0(A_4)) | ~m1_orders_2(C_22, A_4, B_16) | k1_xboole_0=B_16 | ~m1_subset_1(C_22, k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_orders_2(A_4) | ~v5_orders_2(A_4) | ~v4_orders_2(A_4) | ~v3_orders_2(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.50/1.38  tff(c_110, plain, (![A_85, B_86, C_87]: (k3_orders_2(A_85, B_86, '#skF_1'(A_85, B_86, C_87))=C_87 | ~m1_orders_2(C_87, A_85, B_86) | k1_xboole_0=B_86 | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(A_85))) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_orders_2(A_85) | ~v5_orders_2(A_85) | ~v4_orders_2(A_85) | ~v3_orders_2(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.50/1.38  tff(c_112, plain, (![B_86]: (k3_orders_2('#skF_2', B_86, '#skF_1'('#skF_2', B_86, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_86) | k1_xboole_0=B_86 | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_110])).
% 2.50/1.38  tff(c_115, plain, (![B_86]: (k3_orders_2('#skF_2', B_86, '#skF_1'('#skF_2', B_86, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_86) | k1_xboole_0=B_86 | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_112])).
% 2.50/1.38  tff(c_117, plain, (![B_88]: (k3_orders_2('#skF_2', B_88, '#skF_1'('#skF_2', B_88, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_88) | k1_xboole_0=B_88 | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_115])).
% 2.50/1.38  tff(c_119, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_26, c_117])).
% 2.50/1.38  tff(c_122, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_119])).
% 2.50/1.38  tff(c_123, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_67, c_122])).
% 2.50/1.38  tff(c_24, plain, (![A_33, B_41, C_45, D_47]: (r2_orders_2(A_33, B_41, C_45) | ~r2_hidden(B_41, k3_orders_2(A_33, D_47, C_45)) | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_subset_1(C_45, u1_struct_0(A_33)) | ~m1_subset_1(B_41, u1_struct_0(A_33)) | ~l1_orders_2(A_33) | ~v5_orders_2(A_33) | ~v4_orders_2(A_33) | ~v3_orders_2(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.50/1.38  tff(c_126, plain, (![B_41]: (r2_orders_2('#skF_2', B_41, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_41, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_41, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_24])).
% 2.50/1.38  tff(c_132, plain, (![B_41]: (r2_orders_2('#skF_2', B_41, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_41, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_41, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_26, c_126])).
% 2.50/1.38  tff(c_133, plain, (![B_41]: (r2_orders_2('#skF_2', B_41, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_41, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_41, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_132])).
% 2.50/1.38  tff(c_138, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_133])).
% 2.50/1.38  tff(c_141, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_138])).
% 2.50/1.38  tff(c_147, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_26, c_68, c_141])).
% 2.50/1.38  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_67, c_147])).
% 2.50/1.38  tff(c_151, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_133])).
% 2.50/1.38  tff(c_93, plain, (![A_70, B_71, C_72]: (r2_hidden('#skF_1'(A_70, B_71, C_72), B_71) | ~m1_orders_2(C_72, A_70, B_71) | k1_xboole_0=B_71 | ~m1_subset_1(C_72, k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_orders_2(A_70) | ~v5_orders_2(A_70) | ~v4_orders_2(A_70) | ~v3_orders_2(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.50/1.38  tff(c_95, plain, (![B_71]: (r2_hidden('#skF_1'('#skF_2', B_71, '#skF_3'), B_71) | ~m1_orders_2('#skF_3', '#skF_2', B_71) | k1_xboole_0=B_71 | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_93])).
% 2.50/1.38  tff(c_98, plain, (![B_71]: (r2_hidden('#skF_1'('#skF_2', B_71, '#skF_3'), B_71) | ~m1_orders_2('#skF_3', '#skF_2', B_71) | k1_xboole_0=B_71 | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_95])).
% 2.50/1.38  tff(c_101, plain, (![B_77]: (r2_hidden('#skF_1'('#skF_2', B_77, '#skF_3'), B_77) | ~m1_orders_2('#skF_3', '#skF_2', B_77) | k1_xboole_0=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_98])).
% 2.50/1.38  tff(c_103, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | ~m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_26, c_101])).
% 2.50/1.38  tff(c_106, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_103])).
% 2.50/1.38  tff(c_107, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_67, c_106])).
% 2.50/1.38  tff(c_159, plain, (![B_93]: (r2_orders_2('#skF_2', B_93, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_93, '#skF_3') | ~m1_subset_1(B_93, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_133])).
% 2.50/1.38  tff(c_18, plain, (![A_30, B_31, C_32]: (~r2_orders_2(A_30, B_31, B_31) | ~m1_subset_1(C_32, u1_struct_0(A_30)) | ~m1_subset_1(B_31, u1_struct_0(A_30)) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.50/1.38  tff(c_162, plain, (![C_32]: (~m1_subset_1(C_32, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_159, c_18])).
% 2.50/1.38  tff(c_165, plain, (![C_32]: (~m1_subset_1(C_32, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_107, c_28, c_162])).
% 2.50/1.38  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_151])).
% 2.50/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.38  
% 2.50/1.38  Inference rules
% 2.50/1.38  ----------------------
% 2.50/1.38  #Ref     : 0
% 2.50/1.38  #Sup     : 19
% 2.50/1.38  #Fact    : 0
% 2.50/1.38  #Define  : 0
% 2.50/1.38  #Split   : 3
% 2.50/1.38  #Chain   : 0
% 2.50/1.38  #Close   : 0
% 2.50/1.38  
% 2.50/1.38  Ordering : KBO
% 2.50/1.38  
% 2.50/1.38  Simplification rules
% 2.50/1.38  ----------------------
% 2.50/1.38  #Subsume      : 1
% 2.50/1.38  #Demod        : 51
% 2.50/1.38  #Tautology    : 9
% 2.50/1.38  #SimpNegUnit  : 15
% 2.50/1.38  #BackRed      : 2
% 2.50/1.38  
% 2.50/1.38  #Partial instantiations: 0
% 2.50/1.38  #Strategies tried      : 1
% 2.50/1.38  
% 2.50/1.38  Timing (in seconds)
% 2.50/1.38  ----------------------
% 2.50/1.39  Preprocessing        : 0.32
% 2.50/1.39  Parsing              : 0.16
% 2.50/1.39  CNF conversion       : 0.03
% 2.50/1.39  Main loop            : 0.25
% 2.50/1.39  Inferencing          : 0.10
% 2.50/1.39  Reduction            : 0.07
% 2.50/1.39  Demodulation         : 0.04
% 2.50/1.39  BG Simplification    : 0.02
% 2.50/1.39  Subsumption          : 0.04
% 2.50/1.39  Abstraction          : 0.01
% 2.50/1.39  MUC search           : 0.00
% 2.50/1.39  Cooper               : 0.00
% 2.50/1.39  Total                : 0.61
% 2.50/1.39  Index Insertion      : 0.00
% 2.50/1.39  Index Deletion       : 0.00
% 2.50/1.39  Index Matching       : 0.00
% 2.50/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
