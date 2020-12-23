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
% DateTime   : Thu Dec  3 10:19:51 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  196 (2034 expanded)
%              Number of leaves         :   26 ( 773 expanded)
%              Depth                    :   26
%              Number of atoms          :  762 (14204 expanded)
%              Number of equality atoms :   90 ( 863 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
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
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                       => ( ( r2_orders_2(A,B,C)
                            & r2_hidden(B,D)
                            & r2_hidden(C,E)
                            & m1_orders_2(E,A,D) )
                         => r2_hidden(B,E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_orders_2)).

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

tff(f_107,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r2_orders_2(A,B,C)
                      & r2_orders_2(A,C,D) )
                   => r2_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_orders_2)).

tff(c_22,plain,(
    ~ r2_hidden('#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_28,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_26,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_30,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_44,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_42,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_40,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_24,plain,(
    m1_orders_2('#skF_6','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_46,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_368,plain,(
    ! [A_131,B_132,C_133] :
      ( r2_hidden('#skF_1'(A_131,B_132,C_133),B_132)
      | ~ m1_orders_2(C_133,A_131,B_132)
      | k1_xboole_0 = B_132
      | ~ m1_subset_1(C_133,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_orders_2(A_131)
      | ~ v5_orders_2(A_131)
      | ~ v4_orders_2(A_131)
      | ~ v3_orders_2(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_372,plain,(
    ! [B_132] :
      ( r2_hidden('#skF_1'('#skF_2',B_132,'#skF_6'),B_132)
      | ~ m1_orders_2('#skF_6','#skF_2',B_132)
      | k1_xboole_0 = B_132
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_368])).

tff(c_381,plain,(
    ! [B_132] :
      ( r2_hidden('#skF_1'('#skF_2',B_132,'#skF_6'),B_132)
      | ~ m1_orders_2('#skF_6','#skF_2',B_132)
      | k1_xboole_0 = B_132
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_372])).

tff(c_388,plain,(
    ! [B_138] :
      ( r2_hidden('#skF_1'('#skF_2',B_138,'#skF_6'),B_138)
      | ~ m1_orders_2('#skF_6','#skF_2',B_138)
      | k1_xboole_0 = B_138
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_381])).

tff(c_394,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_34,c_388])).

tff(c_399,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_394])).

tff(c_400,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_399])).

tff(c_81,plain,(
    ! [A_87,B_88,C_89] :
      ( r2_hidden('#skF_1'(A_87,B_88,C_89),B_88)
      | ~ m1_orders_2(C_89,A_87,B_88)
      | k1_xboole_0 = B_88
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_orders_2(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v4_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_83,plain,(
    ! [B_88] :
      ( r2_hidden('#skF_1'('#skF_2',B_88,'#skF_6'),B_88)
      | ~ m1_orders_2('#skF_6','#skF_2',B_88)
      | k1_xboole_0 = B_88
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_81])).

tff(c_88,plain,(
    ! [B_88] :
      ( r2_hidden('#skF_1'('#skF_2',B_88,'#skF_6'),B_88)
      | ~ m1_orders_2('#skF_6','#skF_2',B_88)
      | k1_xboole_0 = B_88
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_83])).

tff(c_94,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_1'('#skF_2',B_90,'#skF_6'),B_90)
      | ~ m1_orders_2('#skF_6','#skF_2',B_90)
      | k1_xboole_0 = B_90
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_88])).

tff(c_98,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_34,c_94])).

tff(c_102,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_98])).

tff(c_104,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_50,plain,(
    ! [C_80,A_81] :
      ( k1_xboole_0 = C_80
      | ~ m1_orders_2(C_80,A_81,k1_xboole_0)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_orders_2(A_81)
      | ~ v5_orders_2(A_81)
      | ~ v4_orders_2(A_81)
      | ~ v3_orders_2(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_50])).

tff(c_57,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_52])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_57])).

tff(c_63,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_107,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_63])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_107])).

tff(c_114,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_102])).

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

tff(c_138,plain,(
    ! [A_105,B_106,C_107] :
      ( k3_orders_2(A_105,B_106,'#skF_1'(A_105,B_106,C_107)) = C_107
      | ~ m1_orders_2(C_107,A_105,B_106)
      | k1_xboole_0 = B_106
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_orders_2(A_105)
      | ~ v5_orders_2(A_105)
      | ~ v4_orders_2(A_105)
      | ~ v3_orders_2(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_140,plain,(
    ! [B_106] :
      ( k3_orders_2('#skF_2',B_106,'#skF_1'('#skF_2',B_106,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_106)
      | k1_xboole_0 = B_106
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_138])).

tff(c_145,plain,(
    ! [B_106] :
      ( k3_orders_2('#skF_2',B_106,'#skF_1'('#skF_2',B_106,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_106)
      | k1_xboole_0 = B_106
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_140])).

tff(c_151,plain,(
    ! [B_108] :
      ( k3_orders_2('#skF_2',B_108,'#skF_1'('#skF_2',B_108,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_108)
      | k1_xboole_0 = B_108
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_145])).

tff(c_155,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_34,c_151])).

tff(c_159,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_155])).

tff(c_160,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_159])).

tff(c_18,plain,(
    ! [B_46,D_52,A_38,C_50] :
      ( r2_hidden(B_46,D_52)
      | ~ r2_hidden(B_46,k3_orders_2(A_38,D_52,C_50))
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_subset_1(C_50,u1_struct_0(A_38))
      | ~ m1_subset_1(B_46,u1_struct_0(A_38))
      | ~ l1_orders_2(A_38)
      | ~ v5_orders_2(A_38)
      | ~ v4_orders_2(A_38)
      | ~ v3_orders_2(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_165,plain,(
    ! [B_46] :
      ( r2_hidden(B_46,'#skF_5')
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_18])).

tff(c_172,plain,(
    ! [B_46] :
      ( r2_hidden(B_46,'#skF_5')
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_34,c_165])).

tff(c_173,plain,(
    ! [B_46] :
      ( r2_hidden(B_46,'#skF_5')
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_172])).

tff(c_175,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_178,plain,
    ( ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_175])).

tff(c_181,plain,
    ( k1_xboole_0 = '#skF_5'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_34,c_32,c_24,c_178])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_114,c_181])).

tff(c_185,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_20,plain,(
    ! [A_38,B_46,C_50,D_52] :
      ( r2_orders_2(A_38,B_46,C_50)
      | ~ r2_hidden(B_46,k3_orders_2(A_38,D_52,C_50))
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_subset_1(C_50,u1_struct_0(A_38))
      | ~ m1_subset_1(B_46,u1_struct_0(A_38))
      | ~ l1_orders_2(A_38)
      | ~ v5_orders_2(A_38)
      | ~ v4_orders_2(A_38)
      | ~ v3_orders_2(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_163,plain,(
    ! [B_46] :
      ( r2_orders_2('#skF_2',B_46,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_20])).

tff(c_169,plain,(
    ! [B_46] :
      ( r2_orders_2('#skF_2',B_46,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_34,c_163])).

tff(c_170,plain,(
    ! [B_46] :
      ( r2_orders_2('#skF_2',B_46,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_169])).

tff(c_277,plain,(
    ! [B_123] :
      ( r2_orders_2('#skF_2',B_123,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_123,'#skF_6')
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_170])).

tff(c_14,plain,(
    ! [A_23,B_31,D_37,C_35] :
      ( r2_orders_2(A_23,B_31,D_37)
      | ~ r2_orders_2(A_23,C_35,D_37)
      | ~ r2_orders_2(A_23,B_31,C_35)
      | ~ m1_subset_1(D_37,u1_struct_0(A_23))
      | ~ m1_subset_1(C_35,u1_struct_0(A_23))
      | ~ m1_subset_1(B_31,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_282,plain,(
    ! [B_31,B_123] :
      ( r2_orders_2('#skF_2',B_31,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_orders_2('#skF_2',B_31,B_123)
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ r2_hidden(B_123,'#skF_6')
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_277,c_14])).

tff(c_287,plain,(
    ! [B_124,B_125] :
      ( r2_orders_2('#skF_2',B_124,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_orders_2('#skF_2',B_124,B_125)
      | ~ m1_subset_1(B_124,u1_struct_0('#skF_2'))
      | ~ r2_hidden(B_125,'#skF_6')
      | ~ m1_subset_1(B_125,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_185,c_282])).

tff(c_291,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_287])).

tff(c_297,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_38,c_291])).

tff(c_186,plain,(
    ! [B_109,A_110,D_111,C_112] :
      ( r2_hidden(B_109,k3_orders_2(A_110,D_111,C_112))
      | ~ r2_hidden(B_109,D_111)
      | ~ r2_orders_2(A_110,B_109,C_112)
      | ~ m1_subset_1(D_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m1_subset_1(C_112,u1_struct_0(A_110))
      | ~ m1_subset_1(B_109,u1_struct_0(A_110))
      | ~ l1_orders_2(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v4_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_190,plain,(
    ! [B_109,C_112] :
      ( r2_hidden(B_109,k3_orders_2('#skF_2','#skF_5',C_112))
      | ~ r2_hidden(B_109,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_109,C_112)
      | ~ m1_subset_1(C_112,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_186])).

tff(c_197,plain,(
    ! [B_109,C_112] :
      ( r2_hidden(B_109,k3_orders_2('#skF_2','#skF_5',C_112))
      | ~ r2_hidden(B_109,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_109,C_112)
      | ~ m1_subset_1(C_112,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_190])).

tff(c_250,plain,(
    ! [B_117,C_118] :
      ( r2_hidden(B_117,k3_orders_2('#skF_2','#skF_5',C_118))
      | ~ r2_hidden(B_117,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_117,C_118)
      | ~ m1_subset_1(C_118,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_197])).

tff(c_257,plain,(
    ! [B_117] :
      ( r2_hidden(B_117,'#skF_6')
      | ~ r2_hidden(B_117,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_117,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_250])).

tff(c_267,plain,(
    ! [B_117] :
      ( r2_hidden(B_117,'#skF_6')
      | ~ r2_hidden(B_117,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_117,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_257])).

tff(c_302,plain,
    ( r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_297,c_267])).

tff(c_310,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_302])).

tff(c_312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_310])).

tff(c_313,plain,
    ( ~ m1_orders_2('#skF_6','#skF_2',k1_xboole_0)
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_356,plain,(
    ~ m1_orders_2('#skF_6','#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_403,plain,(
    ~ m1_orders_2('#skF_6','#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_356])).

tff(c_411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_403])).

tff(c_413,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_399])).

tff(c_457,plain,(
    ! [A_150,B_151,C_152] :
      ( k3_orders_2(A_150,B_151,'#skF_1'(A_150,B_151,C_152)) = C_152
      | ~ m1_orders_2(C_152,A_150,B_151)
      | k1_xboole_0 = B_151
      | ~ m1_subset_1(C_152,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_orders_2(A_150)
      | ~ v5_orders_2(A_150)
      | ~ v4_orders_2(A_150)
      | ~ v3_orders_2(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_461,plain,(
    ! [B_151] :
      ( k3_orders_2('#skF_2',B_151,'#skF_1'('#skF_2',B_151,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_151)
      | k1_xboole_0 = B_151
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_457])).

tff(c_470,plain,(
    ! [B_151] :
      ( k3_orders_2('#skF_2',B_151,'#skF_1'('#skF_2',B_151,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_151)
      | k1_xboole_0 = B_151
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_461])).

tff(c_476,plain,(
    ! [B_153] :
      ( k3_orders_2('#skF_2',B_153,'#skF_1'('#skF_2',B_153,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_153)
      | k1_xboole_0 = B_153
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_470])).

tff(c_482,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_34,c_476])).

tff(c_487,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_482])).

tff(c_488,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_487])).

tff(c_493,plain,(
    ! [B_46] :
      ( r2_hidden(B_46,'#skF_5')
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_18])).

tff(c_500,plain,(
    ! [B_46] :
      ( r2_hidden(B_46,'#skF_5')
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_34,c_493])).

tff(c_501,plain,(
    ! [B_46] :
      ( r2_hidden(B_46,'#skF_5')
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_500])).

tff(c_503,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_501])).

tff(c_506,plain,
    ( ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_503])).

tff(c_509,plain,
    ( k1_xboole_0 = '#skF_5'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_34,c_32,c_24,c_506])).

tff(c_511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_413,c_509])).

tff(c_513,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_491,plain,(
    ! [B_46] :
      ( r2_orders_2('#skF_2',B_46,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_20])).

tff(c_497,plain,(
    ! [B_46] :
      ( r2_orders_2('#skF_2',B_46,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_34,c_491])).

tff(c_498,plain,(
    ! [B_46] :
      ( r2_orders_2('#skF_2',B_46,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_497])).

tff(c_635,plain,(
    ! [B_168] :
      ( r2_orders_2('#skF_2',B_168,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_168,'#skF_6')
      | ~ m1_subset_1(B_168,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_498])).

tff(c_640,plain,(
    ! [B_31,B_168] :
      ( r2_orders_2('#skF_2',B_31,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_orders_2('#skF_2',B_31,B_168)
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ r2_hidden(B_168,'#skF_6')
      | ~ m1_subset_1(B_168,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_635,c_14])).

tff(c_645,plain,(
    ! [B_169,B_170] :
      ( r2_orders_2('#skF_2',B_169,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_orders_2('#skF_2',B_169,B_170)
      | ~ m1_subset_1(B_169,u1_struct_0('#skF_2'))
      | ~ r2_hidden(B_170,'#skF_6')
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_513,c_640])).

tff(c_649,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_645])).

tff(c_655,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_38,c_649])).

tff(c_544,plain,(
    ! [B_155,A_156,D_157,C_158] :
      ( r2_hidden(B_155,k3_orders_2(A_156,D_157,C_158))
      | ~ r2_hidden(B_155,D_157)
      | ~ r2_orders_2(A_156,B_155,C_158)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ m1_subset_1(C_158,u1_struct_0(A_156))
      | ~ m1_subset_1(B_155,u1_struct_0(A_156))
      | ~ l1_orders_2(A_156)
      | ~ v5_orders_2(A_156)
      | ~ v4_orders_2(A_156)
      | ~ v3_orders_2(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_550,plain,(
    ! [B_155,C_158] :
      ( r2_hidden(B_155,k3_orders_2('#skF_2','#skF_5',C_158))
      | ~ r2_hidden(B_155,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_155,C_158)
      | ~ m1_subset_1(C_158,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_155,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_544])).

tff(c_561,plain,(
    ! [B_155,C_158] :
      ( r2_hidden(B_155,k3_orders_2('#skF_2','#skF_5',C_158))
      | ~ r2_hidden(B_155,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_155,C_158)
      | ~ m1_subset_1(C_158,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_155,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_550])).

tff(c_601,plain,(
    ! [B_163,C_164] :
      ( r2_hidden(B_163,k3_orders_2('#skF_2','#skF_5',C_164))
      | ~ r2_hidden(B_163,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_163,C_164)
      | ~ m1_subset_1(C_164,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_163,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_561])).

tff(c_608,plain,(
    ! [B_163] :
      ( r2_hidden(B_163,'#skF_6')
      | ~ r2_hidden(B_163,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_163,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_163,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_601])).

tff(c_618,plain,(
    ! [B_163] :
      ( r2_hidden(B_163,'#skF_6')
      | ~ r2_hidden(B_163,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_163,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_163,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_608])).

tff(c_666,plain,
    ( r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_655,c_618])).

tff(c_674,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_666])).

tff(c_676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_674])).

tff(c_677,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_678,plain,(
    m1_orders_2('#skF_6','#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_689,plain,(
    m1_orders_2('#skF_6','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_678])).

tff(c_10,plain,(
    ! [A_1,B_13,C_19] :
      ( r2_hidden('#skF_1'(A_1,B_13,C_19),B_13)
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

tff(c_726,plain,(
    ! [A_182,B_183,C_184] :
      ( r2_hidden('#skF_1'(A_182,B_183,C_184),B_183)
      | ~ m1_orders_2(C_184,A_182,B_183)
      | B_183 = '#skF_6'
      | ~ m1_subset_1(C_184,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_orders_2(A_182)
      | ~ v5_orders_2(A_182)
      | ~ v4_orders_2(A_182)
      | ~ v3_orders_2(A_182)
      | v2_struct_0(A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_10])).

tff(c_728,plain,(
    ! [B_183] :
      ( r2_hidden('#skF_1'('#skF_2',B_183,'#skF_6'),B_183)
      | ~ m1_orders_2('#skF_6','#skF_2',B_183)
      | B_183 = '#skF_6'
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_726])).

tff(c_733,plain,(
    ! [B_183] :
      ( r2_hidden('#skF_1'('#skF_2',B_183,'#skF_6'),B_183)
      | ~ m1_orders_2('#skF_6','#skF_2',B_183)
      | B_183 = '#skF_6'
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_728])).

tff(c_739,plain,(
    ! [B_185] :
      ( r2_hidden('#skF_1'('#skF_2',B_185,'#skF_6'),B_185)
      | ~ m1_orders_2('#skF_6','#skF_2',B_185)
      | B_185 = '#skF_6'
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_733])).

tff(c_743,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_34,c_739])).

tff(c_750,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_743])).

tff(c_758,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_750])).

tff(c_314,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_50])).

tff(c_61,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_54])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_61])).

tff(c_315,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_315])).

tff(c_332,plain,
    ( ~ m1_orders_2('#skF_5','#skF_2',k1_xboole_0)
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_355,plain,(
    ~ m1_orders_2('#skF_5','#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_332])).

tff(c_679,plain,(
    ~ m1_orders_2('#skF_5','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_355])).

tff(c_760,plain,(
    ~ m1_orders_2('#skF_6','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_679])).

tff(c_766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_760])).

tff(c_768,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_750])).

tff(c_771,plain,(
    ! [A_1,B_13,C_19] :
      ( m1_subset_1('#skF_1'(A_1,B_13,C_19),u1_struct_0(A_1))
      | ~ m1_orders_2(C_19,A_1,B_13)
      | B_13 = '#skF_6'
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_12])).

tff(c_8,plain,(
    ! [A_1,B_13,C_19] :
      ( k3_orders_2(A_1,B_13,'#skF_1'(A_1,B_13,C_19)) = C_19
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

tff(c_784,plain,(
    ! [A_196,B_197,C_198] :
      ( k3_orders_2(A_196,B_197,'#skF_1'(A_196,B_197,C_198)) = C_198
      | ~ m1_orders_2(C_198,A_196,B_197)
      | B_197 = '#skF_6'
      | ~ m1_subset_1(C_198,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_orders_2(A_196)
      | ~ v5_orders_2(A_196)
      | ~ v4_orders_2(A_196)
      | ~ v3_orders_2(A_196)
      | v2_struct_0(A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_8])).

tff(c_786,plain,(
    ! [B_197] :
      ( k3_orders_2('#skF_2',B_197,'#skF_1'('#skF_2',B_197,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_197)
      | B_197 = '#skF_6'
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_784])).

tff(c_791,plain,(
    ! [B_197] :
      ( k3_orders_2('#skF_2',B_197,'#skF_1'('#skF_2',B_197,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_197)
      | B_197 = '#skF_6'
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_786])).

tff(c_797,plain,(
    ! [B_199] :
      ( k3_orders_2('#skF_2',B_199,'#skF_1'('#skF_2',B_199,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_199)
      | B_199 = '#skF_6'
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_791])).

tff(c_801,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_34,c_797])).

tff(c_808,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_801])).

tff(c_809,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_768,c_808])).

tff(c_814,plain,(
    ! [B_46] :
      ( r2_hidden(B_46,'#skF_5')
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_18])).

tff(c_821,plain,(
    ! [B_46] :
      ( r2_hidden(B_46,'#skF_5')
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_34,c_814])).

tff(c_822,plain,(
    ! [B_46] :
      ( r2_hidden(B_46,'#skF_5')
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_821])).

tff(c_824,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_822])).

tff(c_827,plain,
    ( ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_771,c_824])).

tff(c_830,plain,
    ( '#skF_5' = '#skF_6'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_34,c_32,c_24,c_827])).

tff(c_832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_768,c_830])).

tff(c_834,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_822])).

tff(c_812,plain,(
    ! [B_46] :
      ( r2_orders_2('#skF_2',B_46,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_20])).

tff(c_818,plain,(
    ! [B_46] :
      ( r2_orders_2('#skF_2',B_46,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_34,c_812])).

tff(c_819,plain,(
    ! [B_46] :
      ( r2_orders_2('#skF_2',B_46,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_818])).

tff(c_920,plain,(
    ! [B_211] :
      ( r2_orders_2('#skF_2',B_211,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_211,'#skF_6')
      | ~ m1_subset_1(B_211,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_819])).

tff(c_925,plain,(
    ! [B_31,B_211] :
      ( r2_orders_2('#skF_2',B_31,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_orders_2('#skF_2',B_31,B_211)
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ r2_hidden(B_211,'#skF_6')
      | ~ m1_subset_1(B_211,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_920,c_14])).

tff(c_937,plain,(
    ! [B_215,B_216] :
      ( r2_orders_2('#skF_2',B_215,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_orders_2('#skF_2',B_215,B_216)
      | ~ m1_subset_1(B_215,u1_struct_0('#skF_2'))
      | ~ r2_hidden(B_216,'#skF_6')
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_834,c_925])).

tff(c_941,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_937])).

tff(c_947,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_38,c_941])).

tff(c_839,plain,(
    ! [B_200,A_201,D_202,C_203] :
      ( r2_hidden(B_200,k3_orders_2(A_201,D_202,C_203))
      | ~ r2_hidden(B_200,D_202)
      | ~ r2_orders_2(A_201,B_200,C_203)
      | ~ m1_subset_1(D_202,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ m1_subset_1(C_203,u1_struct_0(A_201))
      | ~ m1_subset_1(B_200,u1_struct_0(A_201))
      | ~ l1_orders_2(A_201)
      | ~ v5_orders_2(A_201)
      | ~ v4_orders_2(A_201)
      | ~ v3_orders_2(A_201)
      | v2_struct_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_843,plain,(
    ! [B_200,C_203] :
      ( r2_hidden(B_200,k3_orders_2('#skF_2','#skF_5',C_203))
      | ~ r2_hidden(B_200,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_200,C_203)
      | ~ m1_subset_1(C_203,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_200,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_839])).

tff(c_850,plain,(
    ! [B_200,C_203] :
      ( r2_hidden(B_200,k3_orders_2('#skF_2','#skF_5',C_203))
      | ~ r2_hidden(B_200,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_200,C_203)
      | ~ m1_subset_1(C_203,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_200,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_843])).

tff(c_886,plain,(
    ! [B_206,C_207] :
      ( r2_hidden(B_206,k3_orders_2('#skF_2','#skF_5',C_207))
      | ~ r2_hidden(B_206,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_206,C_207)
      | ~ m1_subset_1(C_207,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_206,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_850])).

tff(c_893,plain,(
    ! [B_206] :
      ( r2_hidden(B_206,'#skF_6')
      | ~ r2_hidden(B_206,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_206,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_206,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_886])).

tff(c_903,plain,(
    ! [B_206] :
      ( r2_hidden(B_206,'#skF_6')
      | ~ r2_hidden(B_206,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_206,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_206,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_893])).

tff(c_952,plain,
    ( r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_947,c_903])).

tff(c_960,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_952])).

tff(c_962,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_960])).

tff(c_963,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_976,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_963,c_24,c_963,c_313])).

tff(c_981,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_976,c_28])).

tff(c_984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_981])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:35:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.55  
% 3.54/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.55  %$ r2_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.54/1.55  
% 3.54/1.55  %Foreground sorts:
% 3.54/1.55  
% 3.54/1.55  
% 3.54/1.55  %Background operators:
% 3.54/1.55  
% 3.54/1.55  
% 3.54/1.55  %Foreground operators:
% 3.54/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.54/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.54/1.55  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.54/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.55  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.54/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.54/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.54/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.54/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.54/1.55  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.54/1.55  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.54/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.55  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.54/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.55  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.54/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.54/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.55  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.54/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.54/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.55  
% 3.54/1.59  tff(f_141, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((((r2_orders_2(A, B, C) & r2_hidden(B, D)) & r2_hidden(C, E)) & m1_orders_2(E, A, D)) => r2_hidden(B, E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_orders_2)).
% 3.54/1.59  tff(f_60, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_orders_2)).
% 3.54/1.59  tff(f_107, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 3.54/1.59  tff(f_81, axiom, (![A]: (((v4_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_orders_2(A, B, C) & r2_orders_2(A, C, D)) => r2_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_orders_2)).
% 3.54/1.59  tff(c_22, plain, (~r2_hidden('#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.54/1.59  tff(c_38, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.54/1.59  tff(c_28, plain, (r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.54/1.59  tff(c_36, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.54/1.59  tff(c_26, plain, (r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.54/1.59  tff(c_30, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.54/1.59  tff(c_44, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.54/1.59  tff(c_42, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.54/1.59  tff(c_40, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.54/1.59  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.54/1.59  tff(c_24, plain, (m1_orders_2('#skF_6', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.54/1.59  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.54/1.59  tff(c_46, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.54/1.59  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.54/1.59  tff(c_368, plain, (![A_131, B_132, C_133]: (r2_hidden('#skF_1'(A_131, B_132, C_133), B_132) | ~m1_orders_2(C_133, A_131, B_132) | k1_xboole_0=B_132 | ~m1_subset_1(C_133, k1_zfmisc_1(u1_struct_0(A_131))) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_orders_2(A_131) | ~v5_orders_2(A_131) | ~v4_orders_2(A_131) | ~v3_orders_2(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.54/1.59  tff(c_372, plain, (![B_132]: (r2_hidden('#skF_1'('#skF_2', B_132, '#skF_6'), B_132) | ~m1_orders_2('#skF_6', '#skF_2', B_132) | k1_xboole_0=B_132 | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_368])).
% 3.54/1.59  tff(c_381, plain, (![B_132]: (r2_hidden('#skF_1'('#skF_2', B_132, '#skF_6'), B_132) | ~m1_orders_2('#skF_6', '#skF_2', B_132) | k1_xboole_0=B_132 | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_372])).
% 3.54/1.59  tff(c_388, plain, (![B_138]: (r2_hidden('#skF_1'('#skF_2', B_138, '#skF_6'), B_138) | ~m1_orders_2('#skF_6', '#skF_2', B_138) | k1_xboole_0=B_138 | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_381])).
% 3.54/1.59  tff(c_394, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_34, c_388])).
% 3.54/1.59  tff(c_399, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_394])).
% 3.54/1.59  tff(c_400, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_399])).
% 3.54/1.59  tff(c_81, plain, (![A_87, B_88, C_89]: (r2_hidden('#skF_1'(A_87, B_88, C_89), B_88) | ~m1_orders_2(C_89, A_87, B_88) | k1_xboole_0=B_88 | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_orders_2(A_87) | ~v5_orders_2(A_87) | ~v4_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.54/1.59  tff(c_83, plain, (![B_88]: (r2_hidden('#skF_1'('#skF_2', B_88, '#skF_6'), B_88) | ~m1_orders_2('#skF_6', '#skF_2', B_88) | k1_xboole_0=B_88 | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_81])).
% 3.54/1.59  tff(c_88, plain, (![B_88]: (r2_hidden('#skF_1'('#skF_2', B_88, '#skF_6'), B_88) | ~m1_orders_2('#skF_6', '#skF_2', B_88) | k1_xboole_0=B_88 | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_83])).
% 3.54/1.59  tff(c_94, plain, (![B_90]: (r2_hidden('#skF_1'('#skF_2', B_90, '#skF_6'), B_90) | ~m1_orders_2('#skF_6', '#skF_2', B_90) | k1_xboole_0=B_90 | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_88])).
% 3.54/1.59  tff(c_98, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_34, c_94])).
% 3.54/1.59  tff(c_102, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_98])).
% 3.54/1.59  tff(c_104, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_102])).
% 3.54/1.59  tff(c_50, plain, (![C_80, A_81]: (k1_xboole_0=C_80 | ~m1_orders_2(C_80, A_81, k1_xboole_0) | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_orders_2(A_81) | ~v5_orders_2(A_81) | ~v4_orders_2(A_81) | ~v3_orders_2(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.54/1.59  tff(c_52, plain, (k1_xboole_0='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_50])).
% 3.54/1.59  tff(c_57, plain, (k1_xboole_0='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_52])).
% 3.54/1.59  tff(c_58, plain, (k1_xboole_0='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_57])).
% 3.54/1.59  tff(c_63, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_58])).
% 3.54/1.59  tff(c_107, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_63])).
% 3.54/1.59  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_107])).
% 3.54/1.59  tff(c_114, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_102])).
% 3.54/1.59  tff(c_12, plain, (![A_1, B_13, C_19]: (m1_subset_1('#skF_1'(A_1, B_13, C_19), u1_struct_0(A_1)) | ~m1_orders_2(C_19, A_1, B_13) | k1_xboole_0=B_13 | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1) | ~v4_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.54/1.59  tff(c_138, plain, (![A_105, B_106, C_107]: (k3_orders_2(A_105, B_106, '#skF_1'(A_105, B_106, C_107))=C_107 | ~m1_orders_2(C_107, A_105, B_106) | k1_xboole_0=B_106 | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_orders_2(A_105) | ~v5_orders_2(A_105) | ~v4_orders_2(A_105) | ~v3_orders_2(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.54/1.59  tff(c_140, plain, (![B_106]: (k3_orders_2('#skF_2', B_106, '#skF_1'('#skF_2', B_106, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_106) | k1_xboole_0=B_106 | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_138])).
% 3.54/1.59  tff(c_145, plain, (![B_106]: (k3_orders_2('#skF_2', B_106, '#skF_1'('#skF_2', B_106, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_106) | k1_xboole_0=B_106 | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_140])).
% 3.54/1.59  tff(c_151, plain, (![B_108]: (k3_orders_2('#skF_2', B_108, '#skF_1'('#skF_2', B_108, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_108) | k1_xboole_0=B_108 | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_145])).
% 3.54/1.59  tff(c_155, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_34, c_151])).
% 3.54/1.59  tff(c_159, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_155])).
% 3.54/1.59  tff(c_160, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_114, c_159])).
% 3.54/1.59  tff(c_18, plain, (![B_46, D_52, A_38, C_50]: (r2_hidden(B_46, D_52) | ~r2_hidden(B_46, k3_orders_2(A_38, D_52, C_50)) | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_subset_1(C_50, u1_struct_0(A_38)) | ~m1_subset_1(B_46, u1_struct_0(A_38)) | ~l1_orders_2(A_38) | ~v5_orders_2(A_38) | ~v4_orders_2(A_38) | ~v3_orders_2(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.54/1.59  tff(c_165, plain, (![B_46]: (r2_hidden(B_46, '#skF_5') | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_160, c_18])).
% 3.54/1.59  tff(c_172, plain, (![B_46]: (r2_hidden(B_46, '#skF_5') | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_34, c_165])).
% 3.54/1.59  tff(c_173, plain, (![B_46]: (r2_hidden(B_46, '#skF_5') | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_172])).
% 3.54/1.59  tff(c_175, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_173])).
% 3.54/1.59  tff(c_178, plain, (~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_175])).
% 3.54/1.59  tff(c_181, plain, (k1_xboole_0='#skF_5' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_34, c_32, c_24, c_178])).
% 3.54/1.59  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_114, c_181])).
% 3.54/1.59  tff(c_185, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_173])).
% 3.54/1.59  tff(c_20, plain, (![A_38, B_46, C_50, D_52]: (r2_orders_2(A_38, B_46, C_50) | ~r2_hidden(B_46, k3_orders_2(A_38, D_52, C_50)) | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_subset_1(C_50, u1_struct_0(A_38)) | ~m1_subset_1(B_46, u1_struct_0(A_38)) | ~l1_orders_2(A_38) | ~v5_orders_2(A_38) | ~v4_orders_2(A_38) | ~v3_orders_2(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.54/1.59  tff(c_163, plain, (![B_46]: (r2_orders_2('#skF_2', B_46, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_160, c_20])).
% 3.54/1.59  tff(c_169, plain, (![B_46]: (r2_orders_2('#skF_2', B_46, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_34, c_163])).
% 3.54/1.59  tff(c_170, plain, (![B_46]: (r2_orders_2('#skF_2', B_46, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_169])).
% 3.54/1.59  tff(c_277, plain, (![B_123]: (r2_orders_2('#skF_2', B_123, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_123, '#skF_6') | ~m1_subset_1(B_123, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_170])).
% 3.54/1.59  tff(c_14, plain, (![A_23, B_31, D_37, C_35]: (r2_orders_2(A_23, B_31, D_37) | ~r2_orders_2(A_23, C_35, D_37) | ~r2_orders_2(A_23, B_31, C_35) | ~m1_subset_1(D_37, u1_struct_0(A_23)) | ~m1_subset_1(C_35, u1_struct_0(A_23)) | ~m1_subset_1(B_31, u1_struct_0(A_23)) | ~l1_orders_2(A_23) | ~v5_orders_2(A_23) | ~v4_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.54/1.59  tff(c_282, plain, (![B_31, B_123]: (r2_orders_2('#skF_2', B_31, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_orders_2('#skF_2', B_31, B_123) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_31, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~r2_hidden(B_123, '#skF_6') | ~m1_subset_1(B_123, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_277, c_14])).
% 3.54/1.59  tff(c_287, plain, (![B_124, B_125]: (r2_orders_2('#skF_2', B_124, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_orders_2('#skF_2', B_124, B_125) | ~m1_subset_1(B_124, u1_struct_0('#skF_2')) | ~r2_hidden(B_125, '#skF_6') | ~m1_subset_1(B_125, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_185, c_282])).
% 3.54/1.59  tff(c_291, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~r2_hidden('#skF_4', '#skF_6') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_287])).
% 3.54/1.59  tff(c_297, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_38, c_291])).
% 3.54/1.59  tff(c_186, plain, (![B_109, A_110, D_111, C_112]: (r2_hidden(B_109, k3_orders_2(A_110, D_111, C_112)) | ~r2_hidden(B_109, D_111) | ~r2_orders_2(A_110, B_109, C_112) | ~m1_subset_1(D_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~m1_subset_1(C_112, u1_struct_0(A_110)) | ~m1_subset_1(B_109, u1_struct_0(A_110)) | ~l1_orders_2(A_110) | ~v5_orders_2(A_110) | ~v4_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.54/1.59  tff(c_190, plain, (![B_109, C_112]: (r2_hidden(B_109, k3_orders_2('#skF_2', '#skF_5', C_112)) | ~r2_hidden(B_109, '#skF_5') | ~r2_orders_2('#skF_2', B_109, C_112) | ~m1_subset_1(C_112, u1_struct_0('#skF_2')) | ~m1_subset_1(B_109, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_186])).
% 3.54/1.59  tff(c_197, plain, (![B_109, C_112]: (r2_hidden(B_109, k3_orders_2('#skF_2', '#skF_5', C_112)) | ~r2_hidden(B_109, '#skF_5') | ~r2_orders_2('#skF_2', B_109, C_112) | ~m1_subset_1(C_112, u1_struct_0('#skF_2')) | ~m1_subset_1(B_109, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_190])).
% 3.54/1.59  tff(c_250, plain, (![B_117, C_118]: (r2_hidden(B_117, k3_orders_2('#skF_2', '#skF_5', C_118)) | ~r2_hidden(B_117, '#skF_5') | ~r2_orders_2('#skF_2', B_117, C_118) | ~m1_subset_1(C_118, u1_struct_0('#skF_2')) | ~m1_subset_1(B_117, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_197])).
% 3.54/1.59  tff(c_257, plain, (![B_117]: (r2_hidden(B_117, '#skF_6') | ~r2_hidden(B_117, '#skF_5') | ~r2_orders_2('#skF_2', B_117, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_117, u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_160, c_250])).
% 3.54/1.59  tff(c_267, plain, (![B_117]: (r2_hidden(B_117, '#skF_6') | ~r2_hidden(B_117, '#skF_5') | ~r2_orders_2('#skF_2', B_117, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(B_117, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_257])).
% 3.54/1.59  tff(c_302, plain, (r2_hidden('#skF_3', '#skF_6') | ~r2_hidden('#skF_3', '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_297, c_267])).
% 3.54/1.59  tff(c_310, plain, (r2_hidden('#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28, c_302])).
% 3.54/1.59  tff(c_312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_310])).
% 3.54/1.59  tff(c_313, plain, (~m1_orders_2('#skF_6', '#skF_2', k1_xboole_0) | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_58])).
% 3.54/1.59  tff(c_356, plain, (~m1_orders_2('#skF_6', '#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_313])).
% 3.54/1.59  tff(c_403, plain, (~m1_orders_2('#skF_6', '#skF_2', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_400, c_356])).
% 3.54/1.59  tff(c_411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_403])).
% 3.54/1.59  tff(c_413, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_399])).
% 3.54/1.59  tff(c_457, plain, (![A_150, B_151, C_152]: (k3_orders_2(A_150, B_151, '#skF_1'(A_150, B_151, C_152))=C_152 | ~m1_orders_2(C_152, A_150, B_151) | k1_xboole_0=B_151 | ~m1_subset_1(C_152, k1_zfmisc_1(u1_struct_0(A_150))) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_orders_2(A_150) | ~v5_orders_2(A_150) | ~v4_orders_2(A_150) | ~v3_orders_2(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.54/1.59  tff(c_461, plain, (![B_151]: (k3_orders_2('#skF_2', B_151, '#skF_1'('#skF_2', B_151, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_151) | k1_xboole_0=B_151 | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_457])).
% 3.54/1.59  tff(c_470, plain, (![B_151]: (k3_orders_2('#skF_2', B_151, '#skF_1'('#skF_2', B_151, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_151) | k1_xboole_0=B_151 | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_461])).
% 3.54/1.59  tff(c_476, plain, (![B_153]: (k3_orders_2('#skF_2', B_153, '#skF_1'('#skF_2', B_153, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_153) | k1_xboole_0=B_153 | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_470])).
% 3.54/1.59  tff(c_482, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_34, c_476])).
% 3.54/1.59  tff(c_487, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_482])).
% 3.54/1.59  tff(c_488, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_413, c_487])).
% 3.54/1.59  tff(c_493, plain, (![B_46]: (r2_hidden(B_46, '#skF_5') | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_488, c_18])).
% 3.54/1.59  tff(c_500, plain, (![B_46]: (r2_hidden(B_46, '#skF_5') | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_34, c_493])).
% 3.54/1.59  tff(c_501, plain, (![B_46]: (r2_hidden(B_46, '#skF_5') | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_500])).
% 3.54/1.59  tff(c_503, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_501])).
% 3.54/1.59  tff(c_506, plain, (~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_503])).
% 3.54/1.59  tff(c_509, plain, (k1_xboole_0='#skF_5' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_34, c_32, c_24, c_506])).
% 3.54/1.59  tff(c_511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_413, c_509])).
% 3.54/1.59  tff(c_513, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_501])).
% 3.54/1.59  tff(c_491, plain, (![B_46]: (r2_orders_2('#skF_2', B_46, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_488, c_20])).
% 3.54/1.59  tff(c_497, plain, (![B_46]: (r2_orders_2('#skF_2', B_46, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_34, c_491])).
% 3.54/1.59  tff(c_498, plain, (![B_46]: (r2_orders_2('#skF_2', B_46, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_497])).
% 3.54/1.59  tff(c_635, plain, (![B_168]: (r2_orders_2('#skF_2', B_168, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_168, '#skF_6') | ~m1_subset_1(B_168, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_498])).
% 3.54/1.59  tff(c_640, plain, (![B_31, B_168]: (r2_orders_2('#skF_2', B_31, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_orders_2('#skF_2', B_31, B_168) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_31, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~r2_hidden(B_168, '#skF_6') | ~m1_subset_1(B_168, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_635, c_14])).
% 3.54/1.59  tff(c_645, plain, (![B_169, B_170]: (r2_orders_2('#skF_2', B_169, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_orders_2('#skF_2', B_169, B_170) | ~m1_subset_1(B_169, u1_struct_0('#skF_2')) | ~r2_hidden(B_170, '#skF_6') | ~m1_subset_1(B_170, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_513, c_640])).
% 3.54/1.59  tff(c_649, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~r2_hidden('#skF_4', '#skF_6') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_645])).
% 3.54/1.59  tff(c_655, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_38, c_649])).
% 3.54/1.59  tff(c_544, plain, (![B_155, A_156, D_157, C_158]: (r2_hidden(B_155, k3_orders_2(A_156, D_157, C_158)) | ~r2_hidden(B_155, D_157) | ~r2_orders_2(A_156, B_155, C_158) | ~m1_subset_1(D_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~m1_subset_1(C_158, u1_struct_0(A_156)) | ~m1_subset_1(B_155, u1_struct_0(A_156)) | ~l1_orders_2(A_156) | ~v5_orders_2(A_156) | ~v4_orders_2(A_156) | ~v3_orders_2(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.54/1.59  tff(c_550, plain, (![B_155, C_158]: (r2_hidden(B_155, k3_orders_2('#skF_2', '#skF_5', C_158)) | ~r2_hidden(B_155, '#skF_5') | ~r2_orders_2('#skF_2', B_155, C_158) | ~m1_subset_1(C_158, u1_struct_0('#skF_2')) | ~m1_subset_1(B_155, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_544])).
% 3.54/1.59  tff(c_561, plain, (![B_155, C_158]: (r2_hidden(B_155, k3_orders_2('#skF_2', '#skF_5', C_158)) | ~r2_hidden(B_155, '#skF_5') | ~r2_orders_2('#skF_2', B_155, C_158) | ~m1_subset_1(C_158, u1_struct_0('#skF_2')) | ~m1_subset_1(B_155, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_550])).
% 3.54/1.59  tff(c_601, plain, (![B_163, C_164]: (r2_hidden(B_163, k3_orders_2('#skF_2', '#skF_5', C_164)) | ~r2_hidden(B_163, '#skF_5') | ~r2_orders_2('#skF_2', B_163, C_164) | ~m1_subset_1(C_164, u1_struct_0('#skF_2')) | ~m1_subset_1(B_163, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_561])).
% 3.54/1.59  tff(c_608, plain, (![B_163]: (r2_hidden(B_163, '#skF_6') | ~r2_hidden(B_163, '#skF_5') | ~r2_orders_2('#skF_2', B_163, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_163, u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_488, c_601])).
% 3.54/1.59  tff(c_618, plain, (![B_163]: (r2_hidden(B_163, '#skF_6') | ~r2_hidden(B_163, '#skF_5') | ~r2_orders_2('#skF_2', B_163, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(B_163, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_608])).
% 3.54/1.59  tff(c_666, plain, (r2_hidden('#skF_3', '#skF_6') | ~r2_hidden('#skF_3', '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_655, c_618])).
% 3.54/1.59  tff(c_674, plain, (r2_hidden('#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28, c_666])).
% 3.54/1.59  tff(c_676, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_674])).
% 3.54/1.59  tff(c_677, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_313])).
% 3.54/1.59  tff(c_678, plain, (m1_orders_2('#skF_6', '#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_313])).
% 3.54/1.59  tff(c_689, plain, (m1_orders_2('#skF_6', '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_677, c_678])).
% 3.54/1.59  tff(c_10, plain, (![A_1, B_13, C_19]: (r2_hidden('#skF_1'(A_1, B_13, C_19), B_13) | ~m1_orders_2(C_19, A_1, B_13) | k1_xboole_0=B_13 | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1) | ~v4_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.54/1.59  tff(c_726, plain, (![A_182, B_183, C_184]: (r2_hidden('#skF_1'(A_182, B_183, C_184), B_183) | ~m1_orders_2(C_184, A_182, B_183) | B_183='#skF_6' | ~m1_subset_1(C_184, k1_zfmisc_1(u1_struct_0(A_182))) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_orders_2(A_182) | ~v5_orders_2(A_182) | ~v4_orders_2(A_182) | ~v3_orders_2(A_182) | v2_struct_0(A_182))), inference(demodulation, [status(thm), theory('equality')], [c_677, c_10])).
% 3.54/1.59  tff(c_728, plain, (![B_183]: (r2_hidden('#skF_1'('#skF_2', B_183, '#skF_6'), B_183) | ~m1_orders_2('#skF_6', '#skF_2', B_183) | B_183='#skF_6' | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_726])).
% 3.54/1.59  tff(c_733, plain, (![B_183]: (r2_hidden('#skF_1'('#skF_2', B_183, '#skF_6'), B_183) | ~m1_orders_2('#skF_6', '#skF_2', B_183) | B_183='#skF_6' | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_728])).
% 3.54/1.59  tff(c_739, plain, (![B_185]: (r2_hidden('#skF_1'('#skF_2', B_185, '#skF_6'), B_185) | ~m1_orders_2('#skF_6', '#skF_2', B_185) | B_185='#skF_6' | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_733])).
% 3.54/1.59  tff(c_743, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_34, c_739])).
% 3.54/1.59  tff(c_750, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_743])).
% 3.54/1.59  tff(c_758, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_750])).
% 3.54/1.59  tff(c_314, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_58])).
% 3.54/1.59  tff(c_54, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_50])).
% 3.54/1.59  tff(c_61, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_54])).
% 3.54/1.59  tff(c_62, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_61])).
% 3.54/1.59  tff(c_315, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_62])).
% 3.54/1.59  tff(c_331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_314, c_315])).
% 3.54/1.59  tff(c_332, plain, (~m1_orders_2('#skF_5', '#skF_2', k1_xboole_0) | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_62])).
% 3.54/1.59  tff(c_355, plain, (~m1_orders_2('#skF_5', '#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_332])).
% 3.54/1.59  tff(c_679, plain, (~m1_orders_2('#skF_5', '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_677, c_355])).
% 3.54/1.59  tff(c_760, plain, (~m1_orders_2('#skF_6', '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_758, c_679])).
% 3.54/1.59  tff(c_766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_689, c_760])).
% 3.54/1.59  tff(c_768, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_750])).
% 3.54/1.59  tff(c_771, plain, (![A_1, B_13, C_19]: (m1_subset_1('#skF_1'(A_1, B_13, C_19), u1_struct_0(A_1)) | ~m1_orders_2(C_19, A_1, B_13) | B_13='#skF_6' | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1) | ~v4_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_677, c_12])).
% 3.54/1.59  tff(c_8, plain, (![A_1, B_13, C_19]: (k3_orders_2(A_1, B_13, '#skF_1'(A_1, B_13, C_19))=C_19 | ~m1_orders_2(C_19, A_1, B_13) | k1_xboole_0=B_13 | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1) | ~v4_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.54/1.59  tff(c_784, plain, (![A_196, B_197, C_198]: (k3_orders_2(A_196, B_197, '#skF_1'(A_196, B_197, C_198))=C_198 | ~m1_orders_2(C_198, A_196, B_197) | B_197='#skF_6' | ~m1_subset_1(C_198, k1_zfmisc_1(u1_struct_0(A_196))) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_196))) | ~l1_orders_2(A_196) | ~v5_orders_2(A_196) | ~v4_orders_2(A_196) | ~v3_orders_2(A_196) | v2_struct_0(A_196))), inference(demodulation, [status(thm), theory('equality')], [c_677, c_8])).
% 3.54/1.59  tff(c_786, plain, (![B_197]: (k3_orders_2('#skF_2', B_197, '#skF_1'('#skF_2', B_197, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_197) | B_197='#skF_6' | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_784])).
% 3.54/1.59  tff(c_791, plain, (![B_197]: (k3_orders_2('#skF_2', B_197, '#skF_1'('#skF_2', B_197, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_197) | B_197='#skF_6' | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_786])).
% 3.54/1.59  tff(c_797, plain, (![B_199]: (k3_orders_2('#skF_2', B_199, '#skF_1'('#skF_2', B_199, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_199) | B_199='#skF_6' | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_791])).
% 3.54/1.59  tff(c_801, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_34, c_797])).
% 3.54/1.59  tff(c_808, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_801])).
% 3.54/1.59  tff(c_809, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_768, c_808])).
% 3.54/1.59  tff(c_814, plain, (![B_46]: (r2_hidden(B_46, '#skF_5') | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_809, c_18])).
% 3.54/1.59  tff(c_821, plain, (![B_46]: (r2_hidden(B_46, '#skF_5') | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_34, c_814])).
% 3.54/1.59  tff(c_822, plain, (![B_46]: (r2_hidden(B_46, '#skF_5') | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_821])).
% 3.54/1.59  tff(c_824, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_822])).
% 3.54/1.59  tff(c_827, plain, (~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | '#skF_5'='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_771, c_824])).
% 3.54/1.59  tff(c_830, plain, ('#skF_5'='#skF_6' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_34, c_32, c_24, c_827])).
% 3.54/1.59  tff(c_832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_768, c_830])).
% 3.54/1.59  tff(c_834, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_822])).
% 3.54/1.59  tff(c_812, plain, (![B_46]: (r2_orders_2('#skF_2', B_46, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_809, c_20])).
% 3.54/1.59  tff(c_818, plain, (![B_46]: (r2_orders_2('#skF_2', B_46, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_34, c_812])).
% 3.54/1.59  tff(c_819, plain, (![B_46]: (r2_orders_2('#skF_2', B_46, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_46, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_818])).
% 3.54/1.59  tff(c_920, plain, (![B_211]: (r2_orders_2('#skF_2', B_211, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_211, '#skF_6') | ~m1_subset_1(B_211, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_834, c_819])).
% 3.54/1.59  tff(c_925, plain, (![B_31, B_211]: (r2_orders_2('#skF_2', B_31, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_orders_2('#skF_2', B_31, B_211) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_31, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~r2_hidden(B_211, '#skF_6') | ~m1_subset_1(B_211, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_920, c_14])).
% 3.54/1.59  tff(c_937, plain, (![B_215, B_216]: (r2_orders_2('#skF_2', B_215, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_orders_2('#skF_2', B_215, B_216) | ~m1_subset_1(B_215, u1_struct_0('#skF_2')) | ~r2_hidden(B_216, '#skF_6') | ~m1_subset_1(B_216, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_834, c_925])).
% 3.54/1.59  tff(c_941, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~r2_hidden('#skF_4', '#skF_6') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_937])).
% 3.54/1.59  tff(c_947, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_38, c_941])).
% 3.54/1.59  tff(c_839, plain, (![B_200, A_201, D_202, C_203]: (r2_hidden(B_200, k3_orders_2(A_201, D_202, C_203)) | ~r2_hidden(B_200, D_202) | ~r2_orders_2(A_201, B_200, C_203) | ~m1_subset_1(D_202, k1_zfmisc_1(u1_struct_0(A_201))) | ~m1_subset_1(C_203, u1_struct_0(A_201)) | ~m1_subset_1(B_200, u1_struct_0(A_201)) | ~l1_orders_2(A_201) | ~v5_orders_2(A_201) | ~v4_orders_2(A_201) | ~v3_orders_2(A_201) | v2_struct_0(A_201))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.54/1.59  tff(c_843, plain, (![B_200, C_203]: (r2_hidden(B_200, k3_orders_2('#skF_2', '#skF_5', C_203)) | ~r2_hidden(B_200, '#skF_5') | ~r2_orders_2('#skF_2', B_200, C_203) | ~m1_subset_1(C_203, u1_struct_0('#skF_2')) | ~m1_subset_1(B_200, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_839])).
% 3.54/1.59  tff(c_850, plain, (![B_200, C_203]: (r2_hidden(B_200, k3_orders_2('#skF_2', '#skF_5', C_203)) | ~r2_hidden(B_200, '#skF_5') | ~r2_orders_2('#skF_2', B_200, C_203) | ~m1_subset_1(C_203, u1_struct_0('#skF_2')) | ~m1_subset_1(B_200, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_843])).
% 3.54/1.59  tff(c_886, plain, (![B_206, C_207]: (r2_hidden(B_206, k3_orders_2('#skF_2', '#skF_5', C_207)) | ~r2_hidden(B_206, '#skF_5') | ~r2_orders_2('#skF_2', B_206, C_207) | ~m1_subset_1(C_207, u1_struct_0('#skF_2')) | ~m1_subset_1(B_206, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_850])).
% 3.54/1.59  tff(c_893, plain, (![B_206]: (r2_hidden(B_206, '#skF_6') | ~r2_hidden(B_206, '#skF_5') | ~r2_orders_2('#skF_2', B_206, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_206, u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_809, c_886])).
% 3.54/1.59  tff(c_903, plain, (![B_206]: (r2_hidden(B_206, '#skF_6') | ~r2_hidden(B_206, '#skF_5') | ~r2_orders_2('#skF_2', B_206, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(B_206, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_834, c_893])).
% 3.54/1.59  tff(c_952, plain, (r2_hidden('#skF_3', '#skF_6') | ~r2_hidden('#skF_3', '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_947, c_903])).
% 3.54/1.59  tff(c_960, plain, (r2_hidden('#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28, c_952])).
% 3.54/1.59  tff(c_962, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_960])).
% 3.54/1.59  tff(c_963, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_332])).
% 3.54/1.59  tff(c_976, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_963, c_24, c_963, c_313])).
% 3.54/1.59  tff(c_981, plain, (r2_hidden('#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_976, c_28])).
% 3.54/1.59  tff(c_984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_981])).
% 3.54/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.59  
% 3.54/1.59  Inference rules
% 3.54/1.59  ----------------------
% 3.54/1.59  #Ref     : 0
% 3.54/1.59  #Sup     : 150
% 3.54/1.59  #Fact    : 0
% 3.54/1.59  #Define  : 0
% 3.54/1.59  #Split   : 25
% 3.54/1.59  #Chain   : 0
% 3.54/1.59  #Close   : 0
% 3.54/1.59  
% 3.54/1.59  Ordering : KBO
% 3.54/1.59  
% 3.54/1.59  Simplification rules
% 3.54/1.59  ----------------------
% 3.54/1.59  #Subsume      : 24
% 3.54/1.59  #Demod        : 450
% 3.54/1.59  #Tautology    : 53
% 3.54/1.59  #SimpNegUnit  : 77
% 3.54/1.59  #BackRed      : 32
% 3.54/1.59  
% 3.54/1.59  #Partial instantiations: 0
% 3.54/1.59  #Strategies tried      : 1
% 3.54/1.59  
% 3.54/1.59  Timing (in seconds)
% 3.54/1.59  ----------------------
% 3.54/1.59  Preprocessing        : 0.33
% 3.54/1.59  Parsing              : 0.18
% 3.54/1.59  CNF conversion       : 0.03
% 3.54/1.59  Main loop            : 0.45
% 3.54/1.59  Inferencing          : 0.16
% 3.54/1.59  Reduction            : 0.16
% 3.54/1.59  Demodulation         : 0.11
% 3.54/1.59  BG Simplification    : 0.02
% 3.54/1.59  Subsumption          : 0.09
% 3.54/1.59  Abstraction          : 0.02
% 3.54/1.59  MUC search           : 0.00
% 3.54/1.59  Cooper               : 0.00
% 3.54/1.59  Total                : 0.85
% 3.54/1.59  Index Insertion      : 0.00
% 3.54/1.59  Index Deletion       : 0.00
% 3.54/1.59  Index Matching       : 0.00
% 3.54/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
