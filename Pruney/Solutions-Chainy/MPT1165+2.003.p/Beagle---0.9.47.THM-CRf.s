%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:49 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 466 expanded)
%              Number of leaves         :   27 ( 184 expanded)
%              Depth                    :   20
%              Number of atoms          :  265 (2447 expanded)
%              Number of equality atoms :   32 ( 463 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

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

tff(f_174,negated_conjecture,(
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

tff(f_147,axiom,(
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

tff(f_106,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_121,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r1_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_orders_2)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_48,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_49,plain,(
    ~ m1_orders_2('#skF_3','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_38,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_36,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_34,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_42,plain,
    ( m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_50,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_42])).

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

tff(c_57,plain,(
    ! [A_59] :
      ( m1_orders_2('#skF_3',A_59,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_orders_2(A_59)
      | ~ v5_orders_2(A_59)
      | ~ v4_orders_2(A_59)
      | ~ v3_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_50,c_2])).

tff(c_60,plain,
    ( m1_orders_2('#skF_3','#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_57])).

tff(c_63,plain,
    ( m1_orders_2('#skF_3','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_60])).

tff(c_65,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_49,c_63])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_67,plain,(
    m1_orders_2('#skF_3','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

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

tff(c_113,plain,(
    ! [A_93,B_94,C_95] :
      ( k3_orders_2(A_93,B_94,'#skF_1'(A_93,B_94,C_95)) = C_95
      | ~ m1_orders_2(C_95,A_93,B_94)
      | k1_xboole_0 = B_94
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_orders_2(A_93)
      | ~ v5_orders_2(A_93)
      | ~ v4_orders_2(A_93)
      | ~ v3_orders_2(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_115,plain,(
    ! [B_94] :
      ( k3_orders_2('#skF_2',B_94,'#skF_1'('#skF_2',B_94,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_94)
      | k1_xboole_0 = B_94
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_113])).

tff(c_118,plain,(
    ! [B_94] :
      ( k3_orders_2('#skF_2',B_94,'#skF_1'('#skF_2',B_94,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_94)
      | k1_xboole_0 = B_94
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_115])).

tff(c_120,plain,(
    ! [B_96] :
      ( k3_orders_2('#skF_2',B_96,'#skF_1'('#skF_2',B_96,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_96)
      | k1_xboole_0 = B_96
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_118])).

tff(c_122,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_3')) = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_120])).

tff(c_125,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_122])).

tff(c_126,plain,(
    k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_125])).

tff(c_28,plain,(
    ! [A_40,B_48,C_52,D_54] :
      ( r2_orders_2(A_40,B_48,C_52)
      | ~ r2_hidden(B_48,k3_orders_2(A_40,D_54,C_52))
      | ~ m1_subset_1(D_54,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(C_52,u1_struct_0(A_40))
      | ~ m1_subset_1(B_48,u1_struct_0(A_40))
      | ~ l1_orders_2(A_40)
      | ~ v5_orders_2(A_40)
      | ~ v4_orders_2(A_40)
      | ~ v3_orders_2(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_129,plain,(
    ! [B_48] :
      ( r2_orders_2('#skF_2',B_48,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_48,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_28])).

tff(c_135,plain,(
    ! [B_48] :
      ( r2_orders_2('#skF_2',B_48,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_48,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_129])).

tff(c_136,plain,(
    ! [B_48] :
      ( r2_orders_2('#skF_2',B_48,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_48,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_135])).

tff(c_141,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_144,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_141])).

tff(c_147,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_67,c_144])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_66,c_147])).

tff(c_151,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_91,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_hidden('#skF_1'(A_82,B_83,C_84),B_83)
      | ~ m1_orders_2(C_84,A_82,B_83)
      | k1_xboole_0 = B_83
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_93,plain,(
    ! [B_83] :
      ( r2_hidden('#skF_1'('#skF_2',B_83,'#skF_3'),B_83)
      | ~ m1_orders_2('#skF_3','#skF_2',B_83)
      | k1_xboole_0 = B_83
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_91])).

tff(c_96,plain,(
    ! [B_83] :
      ( r2_hidden('#skF_1'('#skF_2',B_83,'#skF_3'),B_83)
      | ~ m1_orders_2('#skF_3','#skF_2',B_83)
      | k1_xboole_0 = B_83
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_93])).

tff(c_99,plain,(
    ! [B_89] :
      ( r2_hidden('#skF_1'('#skF_2',B_89,'#skF_3'),B_89)
      | ~ m1_orders_2('#skF_3','#skF_2',B_89)
      | k1_xboole_0 = B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_96])).

tff(c_101,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_99])).

tff(c_104,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_101])).

tff(c_105,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_104])).

tff(c_20,plain,(
    ! [A_30,B_31,C_32] :
      ( r3_orders_2(A_30,B_31,B_31)
      | ~ m1_subset_1(C_32,u1_struct_0(A_30))
      | ~ m1_subset_1(B_31,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30)
      | ~ v3_orders_2(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_155,plain,(
    ! [B_31] :
      ( r3_orders_2('#skF_2',B_31,B_31)
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_151,c_20])).

tff(c_162,plain,(
    ! [B_31] :
      ( r3_orders_2('#skF_2',B_31,B_31)
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_155])).

tff(c_171,plain,(
    ! [B_101] :
      ( r3_orders_2('#skF_2',B_101,B_101)
      | ~ m1_subset_1(B_101,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_162])).

tff(c_177,plain,(
    r3_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_1'('#skF_2','#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_151,c_171])).

tff(c_18,plain,(
    ! [A_27,B_28,C_29] :
      ( r1_orders_2(A_27,B_28,C_29)
      | ~ r3_orders_2(A_27,B_28,C_29)
      | ~ m1_subset_1(C_29,u1_struct_0(A_27))
      | ~ m1_subset_1(B_28,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27)
      | ~ v3_orders_2(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_183,plain,
    ( r1_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_1'('#skF_2','#skF_3','#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_177,c_18])).

tff(c_186,plain,
    ( r1_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_1'('#skF_2','#skF_3','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_151,c_183])).

tff(c_187,plain,(
    r1_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_1'('#skF_2','#skF_3','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_186])).

tff(c_195,plain,(
    ! [B_103] :
      ( r2_orders_2('#skF_2',B_103,'#skF_1'('#skF_2','#skF_3','#skF_3'))
      | ~ r2_hidden(B_103,'#skF_3')
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_22,plain,(
    ! [A_33,C_39,B_37] :
      ( ~ r2_orders_2(A_33,C_39,B_37)
      | ~ r1_orders_2(A_33,B_37,C_39)
      | ~ m1_subset_1(C_39,u1_struct_0(A_33))
      | ~ m1_subset_1(B_37,u1_struct_0(A_33))
      | ~ l1_orders_2(A_33)
      | ~ v5_orders_2(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_197,plain,(
    ! [B_103] :
      ( ~ r1_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_3'),B_103)
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ r2_hidden(B_103,'#skF_3')
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_195,c_22])).

tff(c_201,plain,(
    ! [B_104] :
      ( ~ r1_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_3'),B_104)
      | ~ r2_hidden(B_104,'#skF_3')
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_151,c_197])).

tff(c_204,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_187,c_201])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_105,c_204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.36  
% 2.36/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.37  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.36/1.37  
% 2.36/1.37  %Foreground sorts:
% 2.36/1.37  
% 2.36/1.37  
% 2.36/1.37  %Background operators:
% 2.36/1.37  
% 2.36/1.37  
% 2.36/1.37  %Foreground operators:
% 2.36/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.36/1.37  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.36/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.36/1.37  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.36/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.37  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.36/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.37  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.36/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.37  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.36/1.37  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.36/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.37  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.36/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.37  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.36/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.37  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.36/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.36/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.37  
% 2.36/1.39  tff(f_174, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k1_xboole_0) & m1_orders_2(B, A, B)) & ~(~m1_orders_2(B, A, B) & (B = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_orders_2)).
% 2.36/1.39  tff(f_60, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_orders_2)).
% 2.36/1.39  tff(f_147, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 2.36/1.39  tff(f_106, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 2.36/1.39  tff(f_93, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.36/1.39  tff(f_121, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_orders_2)).
% 2.36/1.39  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 2.36/1.39  tff(c_48, plain, (k1_xboole_0!='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 2.36/1.39  tff(c_49, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 2.36/1.39  tff(c_38, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 2.36/1.39  tff(c_36, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 2.36/1.39  tff(c_34, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 2.36/1.39  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 2.36/1.39  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 2.36/1.39  tff(c_42, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_174])).
% 2.66/1.39  tff(c_50, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_49, c_42])).
% 2.66/1.39  tff(c_2, plain, (![A_1]: (m1_orders_2(k1_xboole_0, A_1, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1) | ~v4_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.66/1.39  tff(c_57, plain, (![A_59]: (m1_orders_2('#skF_3', A_59, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_orders_2(A_59) | ~v5_orders_2(A_59) | ~v4_orders_2(A_59) | ~v3_orders_2(A_59) | v2_struct_0(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_50, c_2])).
% 2.66/1.39  tff(c_60, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3') | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_57])).
% 2.66/1.39  tff(c_63, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_60])).
% 2.66/1.39  tff(c_65, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_49, c_63])).
% 2.66/1.39  tff(c_66, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_48])).
% 2.66/1.39  tff(c_67, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 2.66/1.39  tff(c_12, plain, (![A_1, B_13, C_19]: (m1_subset_1('#skF_1'(A_1, B_13, C_19), u1_struct_0(A_1)) | ~m1_orders_2(C_19, A_1, B_13) | k1_xboole_0=B_13 | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1) | ~v4_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.66/1.39  tff(c_113, plain, (![A_93, B_94, C_95]: (k3_orders_2(A_93, B_94, '#skF_1'(A_93, B_94, C_95))=C_95 | ~m1_orders_2(C_95, A_93, B_94) | k1_xboole_0=B_94 | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_orders_2(A_93) | ~v5_orders_2(A_93) | ~v4_orders_2(A_93) | ~v3_orders_2(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.66/1.39  tff(c_115, plain, (![B_94]: (k3_orders_2('#skF_2', B_94, '#skF_1'('#skF_2', B_94, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_94) | k1_xboole_0=B_94 | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_113])).
% 2.66/1.39  tff(c_118, plain, (![B_94]: (k3_orders_2('#skF_2', B_94, '#skF_1'('#skF_2', B_94, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_94) | k1_xboole_0=B_94 | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_115])).
% 2.66/1.39  tff(c_120, plain, (![B_96]: (k3_orders_2('#skF_2', B_96, '#skF_1'('#skF_2', B_96, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_96) | k1_xboole_0=B_96 | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_118])).
% 2.66/1.39  tff(c_122, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_30, c_120])).
% 2.66/1.39  tff(c_125, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_122])).
% 2.66/1.39  tff(c_126, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_66, c_125])).
% 2.66/1.39  tff(c_28, plain, (![A_40, B_48, C_52, D_54]: (r2_orders_2(A_40, B_48, C_52) | ~r2_hidden(B_48, k3_orders_2(A_40, D_54, C_52)) | ~m1_subset_1(D_54, k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(C_52, u1_struct_0(A_40)) | ~m1_subset_1(B_48, u1_struct_0(A_40)) | ~l1_orders_2(A_40) | ~v5_orders_2(A_40) | ~v4_orders_2(A_40) | ~v3_orders_2(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.66/1.39  tff(c_129, plain, (![B_48]: (r2_orders_2('#skF_2', B_48, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_48, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_48, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_28])).
% 2.66/1.39  tff(c_135, plain, (![B_48]: (r2_orders_2('#skF_2', B_48, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_48, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_48, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_129])).
% 2.66/1.39  tff(c_136, plain, (![B_48]: (r2_orders_2('#skF_2', B_48, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_48, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_48, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_135])).
% 2.66/1.39  tff(c_141, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_136])).
% 2.66/1.39  tff(c_144, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_141])).
% 2.66/1.39  tff(c_147, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_67, c_144])).
% 2.66/1.39  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_66, c_147])).
% 2.66/1.39  tff(c_151, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_136])).
% 2.66/1.39  tff(c_91, plain, (![A_82, B_83, C_84]: (r2_hidden('#skF_1'(A_82, B_83, C_84), B_83) | ~m1_orders_2(C_84, A_82, B_83) | k1_xboole_0=B_83 | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(A_82))) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.66/1.39  tff(c_93, plain, (![B_83]: (r2_hidden('#skF_1'('#skF_2', B_83, '#skF_3'), B_83) | ~m1_orders_2('#skF_3', '#skF_2', B_83) | k1_xboole_0=B_83 | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_91])).
% 2.66/1.39  tff(c_96, plain, (![B_83]: (r2_hidden('#skF_1'('#skF_2', B_83, '#skF_3'), B_83) | ~m1_orders_2('#skF_3', '#skF_2', B_83) | k1_xboole_0=B_83 | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_93])).
% 2.66/1.39  tff(c_99, plain, (![B_89]: (r2_hidden('#skF_1'('#skF_2', B_89, '#skF_3'), B_89) | ~m1_orders_2('#skF_3', '#skF_2', B_89) | k1_xboole_0=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_96])).
% 2.66/1.39  tff(c_101, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | ~m1_orders_2('#skF_3', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_30, c_99])).
% 2.66/1.39  tff(c_104, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_101])).
% 2.66/1.39  tff(c_105, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_104])).
% 2.66/1.39  tff(c_20, plain, (![A_30, B_31, C_32]: (r3_orders_2(A_30, B_31, B_31) | ~m1_subset_1(C_32, u1_struct_0(A_30)) | ~m1_subset_1(B_31, u1_struct_0(A_30)) | ~l1_orders_2(A_30) | ~v3_orders_2(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.66/1.39  tff(c_155, plain, (![B_31]: (r3_orders_2('#skF_2', B_31, B_31) | ~m1_subset_1(B_31, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_151, c_20])).
% 2.66/1.39  tff(c_162, plain, (![B_31]: (r3_orders_2('#skF_2', B_31, B_31) | ~m1_subset_1(B_31, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_155])).
% 2.66/1.39  tff(c_171, plain, (![B_101]: (r3_orders_2('#skF_2', B_101, B_101) | ~m1_subset_1(B_101, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_162])).
% 2.66/1.39  tff(c_177, plain, (r3_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_1'('#skF_2', '#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_151, c_171])).
% 2.66/1.39  tff(c_18, plain, (![A_27, B_28, C_29]: (r1_orders_2(A_27, B_28, C_29) | ~r3_orders_2(A_27, B_28, C_29) | ~m1_subset_1(C_29, u1_struct_0(A_27)) | ~m1_subset_1(B_28, u1_struct_0(A_27)) | ~l1_orders_2(A_27) | ~v3_orders_2(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.66/1.39  tff(c_183, plain, (r1_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_177, c_18])).
% 2.66/1.39  tff(c_186, plain, (r1_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_151, c_183])).
% 2.66/1.39  tff(c_187, plain, (r1_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_1'('#skF_2', '#skF_3', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_186])).
% 2.66/1.39  tff(c_195, plain, (![B_103]: (r2_orders_2('#skF_2', B_103, '#skF_1'('#skF_2', '#skF_3', '#skF_3')) | ~r2_hidden(B_103, '#skF_3') | ~m1_subset_1(B_103, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_136])).
% 2.66/1.39  tff(c_22, plain, (![A_33, C_39, B_37]: (~r2_orders_2(A_33, C_39, B_37) | ~r1_orders_2(A_33, B_37, C_39) | ~m1_subset_1(C_39, u1_struct_0(A_33)) | ~m1_subset_1(B_37, u1_struct_0(A_33)) | ~l1_orders_2(A_33) | ~v5_orders_2(A_33))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.66/1.39  tff(c_197, plain, (![B_103]: (~r1_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', '#skF_3'), B_103) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~r2_hidden(B_103, '#skF_3') | ~m1_subset_1(B_103, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_195, c_22])).
% 2.66/1.39  tff(c_201, plain, (![B_104]: (~r1_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', '#skF_3'), B_104) | ~r2_hidden(B_104, '#skF_3') | ~m1_subset_1(B_104, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_151, c_197])).
% 2.66/1.39  tff(c_204, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_187, c_201])).
% 2.66/1.39  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_105, c_204])).
% 2.66/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.39  
% 2.66/1.39  Inference rules
% 2.66/1.39  ----------------------
% 2.66/1.39  #Ref     : 0
% 2.66/1.39  #Sup     : 25
% 2.66/1.39  #Fact    : 0
% 2.66/1.39  #Define  : 0
% 2.66/1.39  #Split   : 3
% 2.66/1.39  #Chain   : 0
% 2.66/1.39  #Close   : 0
% 2.66/1.39  
% 2.66/1.39  Ordering : KBO
% 2.66/1.39  
% 2.66/1.39  Simplification rules
% 2.66/1.39  ----------------------
% 2.66/1.39  #Subsume      : 0
% 2.66/1.39  #Demod        : 67
% 2.66/1.39  #Tautology    : 10
% 2.66/1.39  #SimpNegUnit  : 18
% 2.66/1.39  #BackRed      : 0
% 2.66/1.39  
% 2.66/1.39  #Partial instantiations: 0
% 2.66/1.39  #Strategies tried      : 1
% 2.66/1.39  
% 2.66/1.39  Timing (in seconds)
% 2.66/1.39  ----------------------
% 2.66/1.39  Preprocessing        : 0.36
% 2.66/1.39  Parsing              : 0.19
% 2.66/1.39  CNF conversion       : 0.03
% 2.66/1.39  Main loop            : 0.20
% 2.66/1.39  Inferencing          : 0.07
% 2.66/1.39  Reduction            : 0.06
% 2.66/1.39  Demodulation         : 0.04
% 2.66/1.39  BG Simplification    : 0.02
% 2.66/1.39  Subsumption          : 0.04
% 2.66/1.39  Abstraction          : 0.01
% 2.66/1.39  MUC search           : 0.00
% 2.66/1.39  Cooper               : 0.00
% 2.66/1.39  Total                : 0.60
% 2.66/1.39  Index Insertion      : 0.00
% 2.66/1.39  Index Deletion       : 0.00
% 2.66/1.39  Index Matching       : 0.00
% 2.66/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
