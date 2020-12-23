%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:51 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 4.27s
% Verified   : 
% Statistics : Number of formulae       :  201 (2065 expanded)
%              Number of leaves         :   28 ( 786 expanded)
%              Depth                    :   26
%              Number of atoms          :  780 (14393 expanded)
%              Number of equality atoms :   91 ( 866 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

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

tff(f_160,negated_conjecture,(
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

tff(f_40,axiom,(
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

tff(f_75,axiom,(
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

tff(f_126,axiom,(
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

tff(f_100,axiom,(
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
                 => ( ( ( r2_orders_2(A,B,C)
                        & r1_orders_2(A,C,D) )
                      | ( r1_orders_2(A,B,C)
                        & r2_orders_2(A,C,D) ) )
                   => r2_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_orders_2)).

tff(c_30,plain,(
    ~ r2_hidden('#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_36,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_34,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_48,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_38,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_58,plain,(
    ! [A_88,B_89,C_90] :
      ( r1_orders_2(A_88,B_89,C_90)
      | ~ r2_orders_2(A_88,B_89,C_90)
      | ~ m1_subset_1(C_90,u1_struct_0(A_88))
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ l1_orders_2(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_58])).

tff(c_63,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_60])).

tff(c_52,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_50,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_32,plain,(
    m1_orders_2('#skF_6','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_54,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_537,plain,(
    ! [A_163,B_164,C_165] :
      ( r2_hidden('#skF_1'(A_163,B_164,C_165),B_164)
      | ~ m1_orders_2(C_165,A_163,B_164)
      | k1_xboole_0 = B_164
      | ~ m1_subset_1(C_165,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_orders_2(A_163)
      | ~ v5_orders_2(A_163)
      | ~ v4_orders_2(A_163)
      | ~ v3_orders_2(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_541,plain,(
    ! [B_164] :
      ( r2_hidden('#skF_1'('#skF_2',B_164,'#skF_6'),B_164)
      | ~ m1_orders_2('#skF_6','#skF_2',B_164)
      | k1_xboole_0 = B_164
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_537])).

tff(c_550,plain,(
    ! [B_164] :
      ( r2_hidden('#skF_1'('#skF_2',B_164,'#skF_6'),B_164)
      | ~ m1_orders_2('#skF_6','#skF_2',B_164)
      | k1_xboole_0 = B_164
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_541])).

tff(c_566,plain,(
    ! [B_167] :
      ( r2_hidden('#skF_1'('#skF_2',B_167,'#skF_6'),B_167)
      | ~ m1_orders_2('#skF_6','#skF_2',B_167)
      | k1_xboole_0 = B_167
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_550])).

tff(c_572,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_566])).

tff(c_577,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_572])).

tff(c_578,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_577])).

tff(c_147,plain,(
    ! [A_113,B_114,C_115] :
      ( r2_hidden('#skF_1'(A_113,B_114,C_115),B_114)
      | ~ m1_orders_2(C_115,A_113,B_114)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(C_115,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_orders_2(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v4_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_149,plain,(
    ! [B_114] :
      ( r2_hidden('#skF_1'('#skF_2',B_114,'#skF_6'),B_114)
      | ~ m1_orders_2('#skF_6','#skF_2',B_114)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_147])).

tff(c_154,plain,(
    ! [B_114] :
      ( r2_hidden('#skF_1'('#skF_2',B_114,'#skF_6'),B_114)
      | ~ m1_orders_2('#skF_6','#skF_2',B_114)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_149])).

tff(c_196,plain,(
    ! [B_119] :
      ( r2_hidden('#skF_1'('#skF_2',B_119,'#skF_6'),B_119)
      | ~ m1_orders_2('#skF_6','#skF_2',B_119)
      | k1_xboole_0 = B_119
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_154])).

tff(c_200,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_196])).

tff(c_204,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_200])).

tff(c_205,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_99,plain,(
    ! [C_97,A_98] :
      ( k1_xboole_0 = C_97
      | ~ m1_orders_2(C_97,A_98,k1_xboole_0)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_orders_2(A_98)
      | ~ v5_orders_2(A_98)
      | ~ v4_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_101,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_99])).

tff(c_106,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_101])).

tff(c_107,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_106])).

tff(c_112,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_209,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_112])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_209])).

tff(c_216,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_18,plain,(
    ! [A_8,B_20,C_26] :
      ( m1_subset_1('#skF_1'(A_8,B_20,C_26),u1_struct_0(A_8))
      | ~ m1_orders_2(C_26,A_8,B_20)
      | k1_xboole_0 = B_20
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_261,plain,(
    ! [A_131,B_132,C_133] :
      ( k3_orders_2(A_131,B_132,'#skF_1'(A_131,B_132,C_133)) = C_133
      | ~ m1_orders_2(C_133,A_131,B_132)
      | k1_xboole_0 = B_132
      | ~ m1_subset_1(C_133,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_orders_2(A_131)
      | ~ v5_orders_2(A_131)
      | ~ v4_orders_2(A_131)
      | ~ v3_orders_2(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_263,plain,(
    ! [B_132] :
      ( k3_orders_2('#skF_2',B_132,'#skF_1'('#skF_2',B_132,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_132)
      | k1_xboole_0 = B_132
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_261])).

tff(c_268,plain,(
    ! [B_132] :
      ( k3_orders_2('#skF_2',B_132,'#skF_1'('#skF_2',B_132,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_132)
      | k1_xboole_0 = B_132
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_263])).

tff(c_274,plain,(
    ! [B_134] :
      ( k3_orders_2('#skF_2',B_134,'#skF_1'('#skF_2',B_134,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_134)
      | k1_xboole_0 = B_134
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_268])).

tff(c_278,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_274])).

tff(c_282,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_278])).

tff(c_283,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_282])).

tff(c_26,plain,(
    ! [B_53,D_59,A_45,C_57] :
      ( r2_hidden(B_53,D_59)
      | ~ r2_hidden(B_53,k3_orders_2(A_45,D_59,C_57))
      | ~ m1_subset_1(D_59,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_subset_1(C_57,u1_struct_0(A_45))
      | ~ m1_subset_1(B_53,u1_struct_0(A_45))
      | ~ l1_orders_2(A_45)
      | ~ v5_orders_2(A_45)
      | ~ v4_orders_2(A_45)
      | ~ v3_orders_2(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_288,plain,(
    ! [B_53] :
      ( r2_hidden(B_53,'#skF_5')
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_26])).

tff(c_295,plain,(
    ! [B_53] :
      ( r2_hidden(B_53,'#skF_5')
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_42,c_288])).

tff(c_296,plain,(
    ! [B_53] :
      ( r2_hidden(B_53,'#skF_5')
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_295])).

tff(c_298,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_309,plain,
    ( ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_298])).

tff(c_312,plain,
    ( k1_xboole_0 = '#skF_5'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_42,c_40,c_32,c_309])).

tff(c_314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_216,c_312])).

tff(c_316,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_28,plain,(
    ! [A_45,B_53,C_57,D_59] :
      ( r2_orders_2(A_45,B_53,C_57)
      | ~ r2_hidden(B_53,k3_orders_2(A_45,D_59,C_57))
      | ~ m1_subset_1(D_59,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_subset_1(C_57,u1_struct_0(A_45))
      | ~ m1_subset_1(B_53,u1_struct_0(A_45))
      | ~ l1_orders_2(A_45)
      | ~ v5_orders_2(A_45)
      | ~ v4_orders_2(A_45)
      | ~ v3_orders_2(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_286,plain,(
    ! [B_53] :
      ( r2_orders_2('#skF_2',B_53,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_28])).

tff(c_292,plain,(
    ! [B_53] :
      ( r2_orders_2('#skF_2',B_53,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_42,c_286])).

tff(c_293,plain,(
    ! [B_53] :
      ( r2_orders_2('#skF_2',B_53,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_292])).

tff(c_420,plain,(
    ! [B_147] :
      ( r2_orders_2('#skF_2',B_147,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_147,'#skF_6')
      | ~ m1_subset_1(B_147,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_293])).

tff(c_20,plain,(
    ! [A_30,C_42,D_44,B_38] :
      ( ~ r2_orders_2(A_30,C_42,D_44)
      | ~ r1_orders_2(A_30,B_38,C_42)
      | r2_orders_2(A_30,B_38,D_44)
      | ~ m1_subset_1(D_44,u1_struct_0(A_30))
      | ~ m1_subset_1(C_42,u1_struct_0(A_30))
      | ~ m1_subset_1(B_38,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30)
      | ~ v5_orders_2(A_30)
      | ~ v4_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_425,plain,(
    ! [B_38,B_147] :
      ( ~ r1_orders_2('#skF_2',B_38,B_147)
      | r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ r2_hidden(B_147,'#skF_6')
      | ~ m1_subset_1(B_147,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_420,c_20])).

tff(c_453,plain,(
    ! [B_152,B_153] :
      ( ~ r1_orders_2('#skF_2',B_152,B_153)
      | r2_orders_2('#skF_2',B_152,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_2'))
      | ~ r2_hidden(B_153,'#skF_6')
      | ~ m1_subset_1(B_153,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_316,c_425])).

tff(c_457,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_63,c_453])).

tff(c_463,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_34,c_46,c_457])).

tff(c_364,plain,(
    ! [B_137,A_138,D_139,C_140] :
      ( r2_hidden(B_137,k3_orders_2(A_138,D_139,C_140))
      | ~ r2_hidden(B_137,D_139)
      | ~ r2_orders_2(A_138,B_137,C_140)
      | ~ m1_subset_1(D_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ m1_subset_1(C_140,u1_struct_0(A_138))
      | ~ m1_subset_1(B_137,u1_struct_0(A_138))
      | ~ l1_orders_2(A_138)
      | ~ v5_orders_2(A_138)
      | ~ v4_orders_2(A_138)
      | ~ v3_orders_2(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_368,plain,(
    ! [B_137,C_140] :
      ( r2_hidden(B_137,k3_orders_2('#skF_2','#skF_5',C_140))
      | ~ r2_hidden(B_137,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_137,C_140)
      | ~ m1_subset_1(C_140,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_137,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_364])).

tff(c_375,plain,(
    ! [B_137,C_140] :
      ( r2_hidden(B_137,k3_orders_2('#skF_2','#skF_5',C_140))
      | ~ r2_hidden(B_137,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_137,C_140)
      | ~ m1_subset_1(C_140,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_137,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_368])).

tff(c_399,plain,(
    ! [B_144,C_145] :
      ( r2_hidden(B_144,k3_orders_2('#skF_2','#skF_5',C_145))
      | ~ r2_hidden(B_144,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_144,C_145)
      | ~ m1_subset_1(C_145,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_144,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_375])).

tff(c_406,plain,(
    ! [B_144] :
      ( r2_hidden(B_144,'#skF_6')
      | ~ r2_hidden(B_144,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_144,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_144,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_399])).

tff(c_416,plain,(
    ! [B_144] :
      ( r2_hidden(B_144,'#skF_6')
      | ~ r2_hidden(B_144,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_144,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_144,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_406])).

tff(c_466,plain,
    ( r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_463,c_416])).

tff(c_473,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_36,c_466])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_473])).

tff(c_476,plain,
    ( ~ m1_orders_2('#skF_6','#skF_2',k1_xboole_0)
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_519,plain,(
    ~ m1_orders_2('#skF_6','#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_476])).

tff(c_582,plain,(
    ~ m1_orders_2('#skF_6','#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_519])).

tff(c_590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_582])).

tff(c_592,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_722,plain,(
    ! [A_188,B_189,C_190] :
      ( k3_orders_2(A_188,B_189,'#skF_1'(A_188,B_189,C_190)) = C_190
      | ~ m1_orders_2(C_190,A_188,B_189)
      | k1_xboole_0 = B_189
      | ~ m1_subset_1(C_190,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_orders_2(A_188)
      | ~ v5_orders_2(A_188)
      | ~ v4_orders_2(A_188)
      | ~ v3_orders_2(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_726,plain,(
    ! [B_189] :
      ( k3_orders_2('#skF_2',B_189,'#skF_1'('#skF_2',B_189,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_189)
      | k1_xboole_0 = B_189
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_722])).

tff(c_735,plain,(
    ! [B_189] :
      ( k3_orders_2('#skF_2',B_189,'#skF_1'('#skF_2',B_189,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_189)
      | k1_xboole_0 = B_189
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_726])).

tff(c_741,plain,(
    ! [B_191] :
      ( k3_orders_2('#skF_2',B_191,'#skF_1'('#skF_2',B_191,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_191)
      | k1_xboole_0 = B_191
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_735])).

tff(c_747,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_741])).

tff(c_752,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_747])).

tff(c_753,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_592,c_752])).

tff(c_758,plain,(
    ! [B_53] :
      ( r2_hidden(B_53,'#skF_5')
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_26])).

tff(c_765,plain,(
    ! [B_53] :
      ( r2_hidden(B_53,'#skF_5')
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_42,c_758])).

tff(c_766,plain,(
    ! [B_53] :
      ( r2_hidden(B_53,'#skF_5')
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_765])).

tff(c_768,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_766])).

tff(c_782,plain,
    ( ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_768])).

tff(c_785,plain,
    ( k1_xboole_0 = '#skF_5'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_42,c_40,c_32,c_782])).

tff(c_787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_592,c_785])).

tff(c_789,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_766])).

tff(c_756,plain,(
    ! [B_53] :
      ( r2_orders_2('#skF_2',B_53,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_28])).

tff(c_762,plain,(
    ! [B_53] :
      ( r2_orders_2('#skF_2',B_53,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_42,c_756])).

tff(c_763,plain,(
    ! [B_53] :
      ( r2_orders_2('#skF_2',B_53,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_762])).

tff(c_935,plain,(
    ! [B_210] :
      ( r2_orders_2('#skF_2',B_210,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_210,'#skF_6')
      | ~ m1_subset_1(B_210,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_763])).

tff(c_940,plain,(
    ! [B_38,B_210] :
      ( ~ r1_orders_2('#skF_2',B_38,B_210)
      | r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ r2_hidden(B_210,'#skF_6')
      | ~ m1_subset_1(B_210,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_935,c_20])).

tff(c_972,plain,(
    ! [B_214,B_215] :
      ( ~ r1_orders_2('#skF_2',B_214,B_215)
      | r2_orders_2('#skF_2',B_214,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_214,u1_struct_0('#skF_2'))
      | ~ r2_hidden(B_215,'#skF_6')
      | ~ m1_subset_1(B_215,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_789,c_940])).

tff(c_976,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_63,c_972])).

tff(c_982,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_34,c_46,c_976])).

tff(c_837,plain,(
    ! [B_194,A_195,D_196,C_197] :
      ( r2_hidden(B_194,k3_orders_2(A_195,D_196,C_197))
      | ~ r2_hidden(B_194,D_196)
      | ~ r2_orders_2(A_195,B_194,C_197)
      | ~ m1_subset_1(D_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ m1_subset_1(C_197,u1_struct_0(A_195))
      | ~ m1_subset_1(B_194,u1_struct_0(A_195))
      | ~ l1_orders_2(A_195)
      | ~ v5_orders_2(A_195)
      | ~ v4_orders_2(A_195)
      | ~ v3_orders_2(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_843,plain,(
    ! [B_194,C_197] :
      ( r2_hidden(B_194,k3_orders_2('#skF_2','#skF_5',C_197))
      | ~ r2_hidden(B_194,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_194,C_197)
      | ~ m1_subset_1(C_197,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_194,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_837])).

tff(c_854,plain,(
    ! [B_194,C_197] :
      ( r2_hidden(B_194,k3_orders_2('#skF_2','#skF_5',C_197))
      | ~ r2_hidden(B_194,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_194,C_197)
      | ~ m1_subset_1(C_197,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_194,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_843])).

tff(c_895,plain,(
    ! [B_202,C_203] :
      ( r2_hidden(B_202,k3_orders_2('#skF_2','#skF_5',C_203))
      | ~ r2_hidden(B_202,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_202,C_203)
      | ~ m1_subset_1(C_203,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_202,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_854])).

tff(c_902,plain,(
    ! [B_202] :
      ( r2_hidden(B_202,'#skF_6')
      | ~ r2_hidden(B_202,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_202,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_202,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_895])).

tff(c_912,plain,(
    ! [B_202] :
      ( r2_hidden(B_202,'#skF_6')
      | ~ r2_hidden(B_202,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_202,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_202,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_902])).

tff(c_985,plain,
    ( r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_982,c_912])).

tff(c_992,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_36,c_985])).

tff(c_994,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_992])).

tff(c_995,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_476])).

tff(c_996,plain,(
    m1_orders_2('#skF_6','#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_476])).

tff(c_1007,plain,(
    m1_orders_2('#skF_6','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_996])).

tff(c_16,plain,(
    ! [A_8,B_20,C_26] :
      ( r2_hidden('#skF_1'(A_8,B_20,C_26),B_20)
      | ~ m1_orders_2(C_26,A_8,B_20)
      | k1_xboole_0 = B_20
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1059,plain,(
    ! [A_225,B_226,C_227] :
      ( r2_hidden('#skF_1'(A_225,B_226,C_227),B_226)
      | ~ m1_orders_2(C_227,A_225,B_226)
      | B_226 = '#skF_6'
      | ~ m1_subset_1(C_227,k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ l1_orders_2(A_225)
      | ~ v5_orders_2(A_225)
      | ~ v4_orders_2(A_225)
      | ~ v3_orders_2(A_225)
      | v2_struct_0(A_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_16])).

tff(c_1061,plain,(
    ! [B_226] :
      ( r2_hidden('#skF_1'('#skF_2',B_226,'#skF_6'),B_226)
      | ~ m1_orders_2('#skF_6','#skF_2',B_226)
      | B_226 = '#skF_6'
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_1059])).

tff(c_1066,plain,(
    ! [B_226] :
      ( r2_hidden('#skF_1'('#skF_2',B_226,'#skF_6'),B_226)
      | ~ m1_orders_2('#skF_6','#skF_2',B_226)
      | B_226 = '#skF_6'
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_1061])).

tff(c_1072,plain,(
    ! [B_228] :
      ( r2_hidden('#skF_1'('#skF_2',B_228,'#skF_6'),B_228)
      | ~ m1_orders_2('#skF_6','#skF_2',B_228)
      | B_228 = '#skF_6'
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1066])).

tff(c_1076,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_1072])).

tff(c_1083,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_5','#skF_6'),'#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1076])).

tff(c_1085,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1083])).

tff(c_477,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_103,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_99])).

tff(c_110,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_103])).

tff(c_111,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_110])).

tff(c_478,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_478])).

tff(c_495,plain,
    ( ~ m1_orders_2('#skF_5','#skF_2',k1_xboole_0)
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_518,plain,(
    ~ m1_orders_2('#skF_5','#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_495])).

tff(c_997,plain,(
    ~ m1_orders_2('#skF_5','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_518])).

tff(c_1086,plain,(
    ~ m1_orders_2('#skF_6','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_997])).

tff(c_1092,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1007,c_1086])).

tff(c_1094,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1083])).

tff(c_1105,plain,(
    ! [A_8,B_20,C_26] :
      ( m1_subset_1('#skF_1'(A_8,B_20,C_26),u1_struct_0(A_8))
      | ~ m1_orders_2(C_26,A_8,B_20)
      | B_20 = '#skF_6'
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_18])).

tff(c_14,plain,(
    ! [A_8,B_20,C_26] :
      ( k3_orders_2(A_8,B_20,'#skF_1'(A_8,B_20,C_26)) = C_26
      | ~ m1_orders_2(C_26,A_8,B_20)
      | k1_xboole_0 = B_20
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1178,plain,(
    ! [A_247,B_248,C_249] :
      ( k3_orders_2(A_247,B_248,'#skF_1'(A_247,B_248,C_249)) = C_249
      | ~ m1_orders_2(C_249,A_247,B_248)
      | B_248 = '#skF_6'
      | ~ m1_subset_1(C_249,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ l1_orders_2(A_247)
      | ~ v5_orders_2(A_247)
      | ~ v4_orders_2(A_247)
      | ~ v3_orders_2(A_247)
      | v2_struct_0(A_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_14])).

tff(c_1180,plain,(
    ! [B_248] :
      ( k3_orders_2('#skF_2',B_248,'#skF_1'('#skF_2',B_248,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_248)
      | B_248 = '#skF_6'
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_1178])).

tff(c_1185,plain,(
    ! [B_248] :
      ( k3_orders_2('#skF_2',B_248,'#skF_1'('#skF_2',B_248,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_248)
      | B_248 = '#skF_6'
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_1180])).

tff(c_1191,plain,(
    ! [B_250] :
      ( k3_orders_2('#skF_2',B_250,'#skF_1'('#skF_2',B_250,'#skF_6')) = '#skF_6'
      | ~ m1_orders_2('#skF_6','#skF_2',B_250)
      | B_250 = '#skF_6'
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1185])).

tff(c_1195,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_1191])).

tff(c_1202,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1195])).

tff(c_1203,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2','#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_1094,c_1202])).

tff(c_1208,plain,(
    ! [B_53] :
      ( r2_hidden(B_53,'#skF_5')
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1203,c_26])).

tff(c_1215,plain,(
    ! [B_53] :
      ( r2_hidden(B_53,'#skF_5')
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_42,c_1208])).

tff(c_1216,plain,(
    ! [B_53] :
      ( r2_hidden(B_53,'#skF_5')
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1215])).

tff(c_1218,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1216])).

tff(c_1234,plain,
    ( ~ m1_orders_2('#skF_6','#skF_2','#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1105,c_1218])).

tff(c_1237,plain,
    ( '#skF_5' = '#skF_6'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_42,c_40,c_32,c_1234])).

tff(c_1239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1094,c_1237])).

tff(c_1241,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1216])).

tff(c_1206,plain,(
    ! [B_53] :
      ( r2_orders_2('#skF_2',B_53,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1203,c_28])).

tff(c_1212,plain,(
    ! [B_53] :
      ( r2_orders_2('#skF_2',B_53,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_42,c_1206])).

tff(c_1213,plain,(
    ! [B_53] :
      ( r2_orders_2('#skF_2',B_53,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1212])).

tff(c_1345,plain,(
    ! [B_266] :
      ( r2_orders_2('#skF_2',B_266,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ r2_hidden(B_266,'#skF_6')
      | ~ m1_subset_1(B_266,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1241,c_1213])).

tff(c_1350,plain,(
    ! [B_38,B_266] :
      ( ~ r1_orders_2('#skF_2',B_38,B_266)
      | r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ r2_hidden(B_266,'#skF_6')
      | ~ m1_subset_1(B_266,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1345,c_20])).

tff(c_1372,plain,(
    ! [B_268,B_269] :
      ( ~ r1_orders_2('#skF_2',B_268,B_269)
      | r2_orders_2('#skF_2',B_268,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_268,u1_struct_0('#skF_2'))
      | ~ r2_hidden(B_269,'#skF_6')
      | ~ m1_subset_1(B_269,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_1241,c_1350])).

tff(c_1376,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_63,c_1372])).

tff(c_1382,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_34,c_46,c_1376])).

tff(c_1298,plain,(
    ! [B_257,A_258,D_259,C_260] :
      ( r2_hidden(B_257,k3_orders_2(A_258,D_259,C_260))
      | ~ r2_hidden(B_257,D_259)
      | ~ r2_orders_2(A_258,B_257,C_260)
      | ~ m1_subset_1(D_259,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ m1_subset_1(C_260,u1_struct_0(A_258))
      | ~ m1_subset_1(B_257,u1_struct_0(A_258))
      | ~ l1_orders_2(A_258)
      | ~ v5_orders_2(A_258)
      | ~ v4_orders_2(A_258)
      | ~ v3_orders_2(A_258)
      | v2_struct_0(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1302,plain,(
    ! [B_257,C_260] :
      ( r2_hidden(B_257,k3_orders_2('#skF_2','#skF_5',C_260))
      | ~ r2_hidden(B_257,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_257,C_260)
      | ~ m1_subset_1(C_260,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_257,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_1298])).

tff(c_1309,plain,(
    ! [B_257,C_260] :
      ( r2_hidden(B_257,k3_orders_2('#skF_2','#skF_5',C_260))
      | ~ r2_hidden(B_257,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_257,C_260)
      | ~ m1_subset_1(C_260,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_257,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_1302])).

tff(c_1324,plain,(
    ! [B_263,C_264] :
      ( r2_hidden(B_263,k3_orders_2('#skF_2','#skF_5',C_264))
      | ~ r2_hidden(B_263,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_263,C_264)
      | ~ m1_subset_1(C_264,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_263,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1309])).

tff(c_1331,plain,(
    ! [B_263] :
      ( r2_hidden(B_263,'#skF_6')
      | ~ r2_hidden(B_263,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_263,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_5','#skF_6'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_263,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1203,c_1324])).

tff(c_1341,plain,(
    ! [B_263] :
      ( r2_hidden(B_263,'#skF_6')
      | ~ r2_hidden(B_263,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_263,'#skF_1'('#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_263,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1241,c_1331])).

tff(c_1385,plain,
    ( r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1382,c_1341])).

tff(c_1392,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_36,c_1385])).

tff(c_1394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1392])).

tff(c_1395,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_495])).

tff(c_1415,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1395,c_32,c_1395,c_476])).

tff(c_1420,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1415,c_36])).

tff(c_1423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1420])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:17:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.68  
% 3.93/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.68  %$ r2_orders_2 > r1_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.93/1.68  
% 3.93/1.68  %Foreground sorts:
% 3.93/1.68  
% 3.93/1.68  
% 3.93/1.68  %Background operators:
% 3.93/1.68  
% 3.93/1.68  
% 3.93/1.68  %Foreground operators:
% 3.93/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.93/1.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.93/1.68  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.93/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.93/1.68  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.93/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.93/1.68  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.93/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.93/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.93/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.93/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.93/1.68  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.93/1.68  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.93/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.93/1.68  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.93/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.68  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.93/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.93/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.68  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.93/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.93/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.93/1.68  
% 4.27/1.72  tff(f_160, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((((r2_orders_2(A, B, C) & r2_hidden(B, D)) & r2_hidden(C, E)) & m1_orders_2(E, A, D)) => r2_hidden(B, E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_orders_2)).
% 4.27/1.72  tff(f_40, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 4.27/1.72  tff(f_75, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_orders_2)).
% 4.27/1.72  tff(f_126, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 4.27/1.72  tff(f_100, axiom, (![A]: (((v4_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((r2_orders_2(A, B, C) & r1_orders_2(A, C, D)) | (r1_orders_2(A, B, C) & r2_orders_2(A, C, D))) => r2_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_orders_2)).
% 4.27/1.72  tff(c_30, plain, (~r2_hidden('#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.27/1.72  tff(c_46, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.27/1.72  tff(c_36, plain, (r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.27/1.72  tff(c_44, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.27/1.72  tff(c_34, plain, (r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.27/1.72  tff(c_48, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.27/1.72  tff(c_38, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.27/1.72  tff(c_58, plain, (![A_88, B_89, C_90]: (r1_orders_2(A_88, B_89, C_90) | ~r2_orders_2(A_88, B_89, C_90) | ~m1_subset_1(C_90, u1_struct_0(A_88)) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~l1_orders_2(A_88))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.27/1.72  tff(c_60, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_38, c_58])).
% 4.27/1.72  tff(c_63, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_60])).
% 4.27/1.72  tff(c_52, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.27/1.72  tff(c_50, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.27/1.72  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.27/1.72  tff(c_32, plain, (m1_orders_2('#skF_6', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.27/1.72  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.27/1.72  tff(c_54, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.27/1.72  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.27/1.72  tff(c_537, plain, (![A_163, B_164, C_165]: (r2_hidden('#skF_1'(A_163, B_164, C_165), B_164) | ~m1_orders_2(C_165, A_163, B_164) | k1_xboole_0=B_164 | ~m1_subset_1(C_165, k1_zfmisc_1(u1_struct_0(A_163))) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_orders_2(A_163) | ~v5_orders_2(A_163) | ~v4_orders_2(A_163) | ~v3_orders_2(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.27/1.72  tff(c_541, plain, (![B_164]: (r2_hidden('#skF_1'('#skF_2', B_164, '#skF_6'), B_164) | ~m1_orders_2('#skF_6', '#skF_2', B_164) | k1_xboole_0=B_164 | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_537])).
% 4.27/1.72  tff(c_550, plain, (![B_164]: (r2_hidden('#skF_1'('#skF_2', B_164, '#skF_6'), B_164) | ~m1_orders_2('#skF_6', '#skF_2', B_164) | k1_xboole_0=B_164 | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_541])).
% 4.27/1.72  tff(c_566, plain, (![B_167]: (r2_hidden('#skF_1'('#skF_2', B_167, '#skF_6'), B_167) | ~m1_orders_2('#skF_6', '#skF_2', B_167) | k1_xboole_0=B_167 | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_550])).
% 4.27/1.72  tff(c_572, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_566])).
% 4.27/1.72  tff(c_577, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_572])).
% 4.27/1.72  tff(c_578, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_577])).
% 4.27/1.72  tff(c_147, plain, (![A_113, B_114, C_115]: (r2_hidden('#skF_1'(A_113, B_114, C_115), B_114) | ~m1_orders_2(C_115, A_113, B_114) | k1_xboole_0=B_114 | ~m1_subset_1(C_115, k1_zfmisc_1(u1_struct_0(A_113))) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_orders_2(A_113) | ~v5_orders_2(A_113) | ~v4_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.27/1.72  tff(c_149, plain, (![B_114]: (r2_hidden('#skF_1'('#skF_2', B_114, '#skF_6'), B_114) | ~m1_orders_2('#skF_6', '#skF_2', B_114) | k1_xboole_0=B_114 | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_147])).
% 4.27/1.72  tff(c_154, plain, (![B_114]: (r2_hidden('#skF_1'('#skF_2', B_114, '#skF_6'), B_114) | ~m1_orders_2('#skF_6', '#skF_2', B_114) | k1_xboole_0=B_114 | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_149])).
% 4.27/1.72  tff(c_196, plain, (![B_119]: (r2_hidden('#skF_1'('#skF_2', B_119, '#skF_6'), B_119) | ~m1_orders_2('#skF_6', '#skF_2', B_119) | k1_xboole_0=B_119 | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_154])).
% 4.27/1.72  tff(c_200, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_196])).
% 4.27/1.72  tff(c_204, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_200])).
% 4.27/1.72  tff(c_205, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_204])).
% 4.27/1.72  tff(c_99, plain, (![C_97, A_98]: (k1_xboole_0=C_97 | ~m1_orders_2(C_97, A_98, k1_xboole_0) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(A_98))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_orders_2(A_98) | ~v5_orders_2(A_98) | ~v4_orders_2(A_98) | ~v3_orders_2(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.27/1.72  tff(c_101, plain, (k1_xboole_0='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_99])).
% 4.27/1.72  tff(c_106, plain, (k1_xboole_0='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_101])).
% 4.27/1.72  tff(c_107, plain, (k1_xboole_0='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_106])).
% 4.27/1.72  tff(c_112, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_107])).
% 4.27/1.72  tff(c_209, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_112])).
% 4.27/1.72  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_209])).
% 4.27/1.72  tff(c_216, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_204])).
% 4.27/1.72  tff(c_18, plain, (![A_8, B_20, C_26]: (m1_subset_1('#skF_1'(A_8, B_20, C_26), u1_struct_0(A_8)) | ~m1_orders_2(C_26, A_8, B_20) | k1_xboole_0=B_20 | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_orders_2(A_8) | ~v5_orders_2(A_8) | ~v4_orders_2(A_8) | ~v3_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.27/1.72  tff(c_261, plain, (![A_131, B_132, C_133]: (k3_orders_2(A_131, B_132, '#skF_1'(A_131, B_132, C_133))=C_133 | ~m1_orders_2(C_133, A_131, B_132) | k1_xboole_0=B_132 | ~m1_subset_1(C_133, k1_zfmisc_1(u1_struct_0(A_131))) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_orders_2(A_131) | ~v5_orders_2(A_131) | ~v4_orders_2(A_131) | ~v3_orders_2(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.27/1.72  tff(c_263, plain, (![B_132]: (k3_orders_2('#skF_2', B_132, '#skF_1'('#skF_2', B_132, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_132) | k1_xboole_0=B_132 | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_261])).
% 4.27/1.72  tff(c_268, plain, (![B_132]: (k3_orders_2('#skF_2', B_132, '#skF_1'('#skF_2', B_132, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_132) | k1_xboole_0=B_132 | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_263])).
% 4.27/1.72  tff(c_274, plain, (![B_134]: (k3_orders_2('#skF_2', B_134, '#skF_1'('#skF_2', B_134, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_134) | k1_xboole_0=B_134 | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_268])).
% 4.27/1.72  tff(c_278, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_274])).
% 4.27/1.72  tff(c_282, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_278])).
% 4.27/1.72  tff(c_283, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_216, c_282])).
% 4.27/1.72  tff(c_26, plain, (![B_53, D_59, A_45, C_57]: (r2_hidden(B_53, D_59) | ~r2_hidden(B_53, k3_orders_2(A_45, D_59, C_57)) | ~m1_subset_1(D_59, k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_subset_1(C_57, u1_struct_0(A_45)) | ~m1_subset_1(B_53, u1_struct_0(A_45)) | ~l1_orders_2(A_45) | ~v5_orders_2(A_45) | ~v4_orders_2(A_45) | ~v3_orders_2(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.27/1.72  tff(c_288, plain, (![B_53]: (r2_hidden(B_53, '#skF_5') | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_283, c_26])).
% 4.27/1.72  tff(c_295, plain, (![B_53]: (r2_hidden(B_53, '#skF_5') | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_42, c_288])).
% 4.27/1.72  tff(c_296, plain, (![B_53]: (r2_hidden(B_53, '#skF_5') | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_295])).
% 4.27/1.72  tff(c_298, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_296])).
% 4.27/1.72  tff(c_309, plain, (~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_298])).
% 4.27/1.72  tff(c_312, plain, (k1_xboole_0='#skF_5' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_42, c_40, c_32, c_309])).
% 4.27/1.72  tff(c_314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_216, c_312])).
% 4.27/1.72  tff(c_316, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_296])).
% 4.27/1.72  tff(c_28, plain, (![A_45, B_53, C_57, D_59]: (r2_orders_2(A_45, B_53, C_57) | ~r2_hidden(B_53, k3_orders_2(A_45, D_59, C_57)) | ~m1_subset_1(D_59, k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_subset_1(C_57, u1_struct_0(A_45)) | ~m1_subset_1(B_53, u1_struct_0(A_45)) | ~l1_orders_2(A_45) | ~v5_orders_2(A_45) | ~v4_orders_2(A_45) | ~v3_orders_2(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.27/1.72  tff(c_286, plain, (![B_53]: (r2_orders_2('#skF_2', B_53, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_283, c_28])).
% 4.27/1.72  tff(c_292, plain, (![B_53]: (r2_orders_2('#skF_2', B_53, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_42, c_286])).
% 4.27/1.72  tff(c_293, plain, (![B_53]: (r2_orders_2('#skF_2', B_53, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_292])).
% 4.27/1.72  tff(c_420, plain, (![B_147]: (r2_orders_2('#skF_2', B_147, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_147, '#skF_6') | ~m1_subset_1(B_147, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_316, c_293])).
% 4.27/1.72  tff(c_20, plain, (![A_30, C_42, D_44, B_38]: (~r2_orders_2(A_30, C_42, D_44) | ~r1_orders_2(A_30, B_38, C_42) | r2_orders_2(A_30, B_38, D_44) | ~m1_subset_1(D_44, u1_struct_0(A_30)) | ~m1_subset_1(C_42, u1_struct_0(A_30)) | ~m1_subset_1(B_38, u1_struct_0(A_30)) | ~l1_orders_2(A_30) | ~v5_orders_2(A_30) | ~v4_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.27/1.72  tff(c_425, plain, (![B_38, B_147]: (~r1_orders_2('#skF_2', B_38, B_147) | r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~r2_hidden(B_147, '#skF_6') | ~m1_subset_1(B_147, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_420, c_20])).
% 4.27/1.72  tff(c_453, plain, (![B_152, B_153]: (~r1_orders_2('#skF_2', B_152, B_153) | r2_orders_2('#skF_2', B_152, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(B_152, u1_struct_0('#skF_2')) | ~r2_hidden(B_153, '#skF_6') | ~m1_subset_1(B_153, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_316, c_425])).
% 4.27/1.72  tff(c_457, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~r2_hidden('#skF_4', '#skF_6') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_63, c_453])).
% 4.27/1.72  tff(c_463, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_34, c_46, c_457])).
% 4.27/1.72  tff(c_364, plain, (![B_137, A_138, D_139, C_140]: (r2_hidden(B_137, k3_orders_2(A_138, D_139, C_140)) | ~r2_hidden(B_137, D_139) | ~r2_orders_2(A_138, B_137, C_140) | ~m1_subset_1(D_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~m1_subset_1(C_140, u1_struct_0(A_138)) | ~m1_subset_1(B_137, u1_struct_0(A_138)) | ~l1_orders_2(A_138) | ~v5_orders_2(A_138) | ~v4_orders_2(A_138) | ~v3_orders_2(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.27/1.72  tff(c_368, plain, (![B_137, C_140]: (r2_hidden(B_137, k3_orders_2('#skF_2', '#skF_5', C_140)) | ~r2_hidden(B_137, '#skF_5') | ~r2_orders_2('#skF_2', B_137, C_140) | ~m1_subset_1(C_140, u1_struct_0('#skF_2')) | ~m1_subset_1(B_137, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_364])).
% 4.27/1.72  tff(c_375, plain, (![B_137, C_140]: (r2_hidden(B_137, k3_orders_2('#skF_2', '#skF_5', C_140)) | ~r2_hidden(B_137, '#skF_5') | ~r2_orders_2('#skF_2', B_137, C_140) | ~m1_subset_1(C_140, u1_struct_0('#skF_2')) | ~m1_subset_1(B_137, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_368])).
% 4.27/1.72  tff(c_399, plain, (![B_144, C_145]: (r2_hidden(B_144, k3_orders_2('#skF_2', '#skF_5', C_145)) | ~r2_hidden(B_144, '#skF_5') | ~r2_orders_2('#skF_2', B_144, C_145) | ~m1_subset_1(C_145, u1_struct_0('#skF_2')) | ~m1_subset_1(B_144, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_375])).
% 4.27/1.72  tff(c_406, plain, (![B_144]: (r2_hidden(B_144, '#skF_6') | ~r2_hidden(B_144, '#skF_5') | ~r2_orders_2('#skF_2', B_144, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_144, u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_283, c_399])).
% 4.27/1.72  tff(c_416, plain, (![B_144]: (r2_hidden(B_144, '#skF_6') | ~r2_hidden(B_144, '#skF_5') | ~r2_orders_2('#skF_2', B_144, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(B_144, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_316, c_406])).
% 4.27/1.72  tff(c_466, plain, (r2_hidden('#skF_3', '#skF_6') | ~r2_hidden('#skF_3', '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_463, c_416])).
% 4.27/1.72  tff(c_473, plain, (r2_hidden('#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_36, c_466])).
% 4.27/1.72  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_473])).
% 4.27/1.72  tff(c_476, plain, (~m1_orders_2('#skF_6', '#skF_2', k1_xboole_0) | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_107])).
% 4.27/1.72  tff(c_519, plain, (~m1_orders_2('#skF_6', '#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_476])).
% 4.27/1.72  tff(c_582, plain, (~m1_orders_2('#skF_6', '#skF_2', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_578, c_519])).
% 4.27/1.72  tff(c_590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_582])).
% 4.27/1.72  tff(c_592, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_577])).
% 4.27/1.72  tff(c_722, plain, (![A_188, B_189, C_190]: (k3_orders_2(A_188, B_189, '#skF_1'(A_188, B_189, C_190))=C_190 | ~m1_orders_2(C_190, A_188, B_189) | k1_xboole_0=B_189 | ~m1_subset_1(C_190, k1_zfmisc_1(u1_struct_0(A_188))) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_orders_2(A_188) | ~v5_orders_2(A_188) | ~v4_orders_2(A_188) | ~v3_orders_2(A_188) | v2_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.27/1.72  tff(c_726, plain, (![B_189]: (k3_orders_2('#skF_2', B_189, '#skF_1'('#skF_2', B_189, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_189) | k1_xboole_0=B_189 | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_722])).
% 4.27/1.72  tff(c_735, plain, (![B_189]: (k3_orders_2('#skF_2', B_189, '#skF_1'('#skF_2', B_189, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_189) | k1_xboole_0=B_189 | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_726])).
% 4.27/1.72  tff(c_741, plain, (![B_191]: (k3_orders_2('#skF_2', B_191, '#skF_1'('#skF_2', B_191, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_191) | k1_xboole_0=B_191 | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_735])).
% 4.27/1.72  tff(c_747, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_741])).
% 4.27/1.72  tff(c_752, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_747])).
% 4.27/1.72  tff(c_753, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_592, c_752])).
% 4.27/1.72  tff(c_758, plain, (![B_53]: (r2_hidden(B_53, '#skF_5') | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_753, c_26])).
% 4.27/1.72  tff(c_765, plain, (![B_53]: (r2_hidden(B_53, '#skF_5') | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_42, c_758])).
% 4.27/1.72  tff(c_766, plain, (![B_53]: (r2_hidden(B_53, '#skF_5') | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_765])).
% 4.27/1.72  tff(c_768, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_766])).
% 4.27/1.72  tff(c_782, plain, (~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_768])).
% 4.27/1.72  tff(c_785, plain, (k1_xboole_0='#skF_5' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_42, c_40, c_32, c_782])).
% 4.27/1.72  tff(c_787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_592, c_785])).
% 4.27/1.72  tff(c_789, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_766])).
% 4.27/1.72  tff(c_756, plain, (![B_53]: (r2_orders_2('#skF_2', B_53, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_753, c_28])).
% 4.27/1.72  tff(c_762, plain, (![B_53]: (r2_orders_2('#skF_2', B_53, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_42, c_756])).
% 4.27/1.72  tff(c_763, plain, (![B_53]: (r2_orders_2('#skF_2', B_53, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_762])).
% 4.27/1.72  tff(c_935, plain, (![B_210]: (r2_orders_2('#skF_2', B_210, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_210, '#skF_6') | ~m1_subset_1(B_210, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_789, c_763])).
% 4.27/1.72  tff(c_940, plain, (![B_38, B_210]: (~r1_orders_2('#skF_2', B_38, B_210) | r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~r2_hidden(B_210, '#skF_6') | ~m1_subset_1(B_210, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_935, c_20])).
% 4.27/1.72  tff(c_972, plain, (![B_214, B_215]: (~r1_orders_2('#skF_2', B_214, B_215) | r2_orders_2('#skF_2', B_214, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(B_214, u1_struct_0('#skF_2')) | ~r2_hidden(B_215, '#skF_6') | ~m1_subset_1(B_215, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_789, c_940])).
% 4.27/1.72  tff(c_976, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~r2_hidden('#skF_4', '#skF_6') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_63, c_972])).
% 4.27/1.72  tff(c_982, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_34, c_46, c_976])).
% 4.27/1.72  tff(c_837, plain, (![B_194, A_195, D_196, C_197]: (r2_hidden(B_194, k3_orders_2(A_195, D_196, C_197)) | ~r2_hidden(B_194, D_196) | ~r2_orders_2(A_195, B_194, C_197) | ~m1_subset_1(D_196, k1_zfmisc_1(u1_struct_0(A_195))) | ~m1_subset_1(C_197, u1_struct_0(A_195)) | ~m1_subset_1(B_194, u1_struct_0(A_195)) | ~l1_orders_2(A_195) | ~v5_orders_2(A_195) | ~v4_orders_2(A_195) | ~v3_orders_2(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.27/1.72  tff(c_843, plain, (![B_194, C_197]: (r2_hidden(B_194, k3_orders_2('#skF_2', '#skF_5', C_197)) | ~r2_hidden(B_194, '#skF_5') | ~r2_orders_2('#skF_2', B_194, C_197) | ~m1_subset_1(C_197, u1_struct_0('#skF_2')) | ~m1_subset_1(B_194, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_837])).
% 4.27/1.72  tff(c_854, plain, (![B_194, C_197]: (r2_hidden(B_194, k3_orders_2('#skF_2', '#skF_5', C_197)) | ~r2_hidden(B_194, '#skF_5') | ~r2_orders_2('#skF_2', B_194, C_197) | ~m1_subset_1(C_197, u1_struct_0('#skF_2')) | ~m1_subset_1(B_194, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_843])).
% 4.27/1.72  tff(c_895, plain, (![B_202, C_203]: (r2_hidden(B_202, k3_orders_2('#skF_2', '#skF_5', C_203)) | ~r2_hidden(B_202, '#skF_5') | ~r2_orders_2('#skF_2', B_202, C_203) | ~m1_subset_1(C_203, u1_struct_0('#skF_2')) | ~m1_subset_1(B_202, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_854])).
% 4.27/1.72  tff(c_902, plain, (![B_202]: (r2_hidden(B_202, '#skF_6') | ~r2_hidden(B_202, '#skF_5') | ~r2_orders_2('#skF_2', B_202, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_202, u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_753, c_895])).
% 4.27/1.72  tff(c_912, plain, (![B_202]: (r2_hidden(B_202, '#skF_6') | ~r2_hidden(B_202, '#skF_5') | ~r2_orders_2('#skF_2', B_202, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(B_202, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_789, c_902])).
% 4.27/1.72  tff(c_985, plain, (r2_hidden('#skF_3', '#skF_6') | ~r2_hidden('#skF_3', '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_982, c_912])).
% 4.27/1.72  tff(c_992, plain, (r2_hidden('#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_36, c_985])).
% 4.27/1.72  tff(c_994, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_992])).
% 4.27/1.72  tff(c_995, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_476])).
% 4.27/1.72  tff(c_996, plain, (m1_orders_2('#skF_6', '#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_476])).
% 4.27/1.72  tff(c_1007, plain, (m1_orders_2('#skF_6', '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_995, c_996])).
% 4.27/1.72  tff(c_16, plain, (![A_8, B_20, C_26]: (r2_hidden('#skF_1'(A_8, B_20, C_26), B_20) | ~m1_orders_2(C_26, A_8, B_20) | k1_xboole_0=B_20 | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_orders_2(A_8) | ~v5_orders_2(A_8) | ~v4_orders_2(A_8) | ~v3_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.27/1.72  tff(c_1059, plain, (![A_225, B_226, C_227]: (r2_hidden('#skF_1'(A_225, B_226, C_227), B_226) | ~m1_orders_2(C_227, A_225, B_226) | B_226='#skF_6' | ~m1_subset_1(C_227, k1_zfmisc_1(u1_struct_0(A_225))) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_225))) | ~l1_orders_2(A_225) | ~v5_orders_2(A_225) | ~v4_orders_2(A_225) | ~v3_orders_2(A_225) | v2_struct_0(A_225))), inference(demodulation, [status(thm), theory('equality')], [c_995, c_16])).
% 4.27/1.72  tff(c_1061, plain, (![B_226]: (r2_hidden('#skF_1'('#skF_2', B_226, '#skF_6'), B_226) | ~m1_orders_2('#skF_6', '#skF_2', B_226) | B_226='#skF_6' | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_1059])).
% 4.27/1.72  tff(c_1066, plain, (![B_226]: (r2_hidden('#skF_1'('#skF_2', B_226, '#skF_6'), B_226) | ~m1_orders_2('#skF_6', '#skF_2', B_226) | B_226='#skF_6' | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_1061])).
% 4.27/1.72  tff(c_1072, plain, (![B_228]: (r2_hidden('#skF_1'('#skF_2', B_228, '#skF_6'), B_228) | ~m1_orders_2('#skF_6', '#skF_2', B_228) | B_228='#skF_6' | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_1066])).
% 4.27/1.72  tff(c_1076, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_42, c_1072])).
% 4.27/1.72  tff(c_1083, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_5', '#skF_6'), '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1076])).
% 4.27/1.72  tff(c_1085, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_1083])).
% 4.27/1.72  tff(c_477, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_107])).
% 4.27/1.72  tff(c_103, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_99])).
% 4.27/1.72  tff(c_110, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_103])).
% 4.27/1.72  tff(c_111, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_110])).
% 4.27/1.72  tff(c_478, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_111])).
% 4.27/1.72  tff(c_494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_477, c_478])).
% 4.27/1.72  tff(c_495, plain, (~m1_orders_2('#skF_5', '#skF_2', k1_xboole_0) | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_111])).
% 4.27/1.72  tff(c_518, plain, (~m1_orders_2('#skF_5', '#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_495])).
% 4.27/1.72  tff(c_997, plain, (~m1_orders_2('#skF_5', '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_995, c_518])).
% 4.27/1.72  tff(c_1086, plain, (~m1_orders_2('#skF_6', '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_997])).
% 4.27/1.72  tff(c_1092, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1007, c_1086])).
% 4.27/1.72  tff(c_1094, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_1083])).
% 4.27/1.72  tff(c_1105, plain, (![A_8, B_20, C_26]: (m1_subset_1('#skF_1'(A_8, B_20, C_26), u1_struct_0(A_8)) | ~m1_orders_2(C_26, A_8, B_20) | B_20='#skF_6' | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_orders_2(A_8) | ~v5_orders_2(A_8) | ~v4_orders_2(A_8) | ~v3_orders_2(A_8) | v2_struct_0(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_995, c_18])).
% 4.27/1.72  tff(c_14, plain, (![A_8, B_20, C_26]: (k3_orders_2(A_8, B_20, '#skF_1'(A_8, B_20, C_26))=C_26 | ~m1_orders_2(C_26, A_8, B_20) | k1_xboole_0=B_20 | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_orders_2(A_8) | ~v5_orders_2(A_8) | ~v4_orders_2(A_8) | ~v3_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.27/1.72  tff(c_1178, plain, (![A_247, B_248, C_249]: (k3_orders_2(A_247, B_248, '#skF_1'(A_247, B_248, C_249))=C_249 | ~m1_orders_2(C_249, A_247, B_248) | B_248='#skF_6' | ~m1_subset_1(C_249, k1_zfmisc_1(u1_struct_0(A_247))) | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0(A_247))) | ~l1_orders_2(A_247) | ~v5_orders_2(A_247) | ~v4_orders_2(A_247) | ~v3_orders_2(A_247) | v2_struct_0(A_247))), inference(demodulation, [status(thm), theory('equality')], [c_995, c_14])).
% 4.27/1.72  tff(c_1180, plain, (![B_248]: (k3_orders_2('#skF_2', B_248, '#skF_1'('#skF_2', B_248, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_248) | B_248='#skF_6' | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_1178])).
% 4.27/1.72  tff(c_1185, plain, (![B_248]: (k3_orders_2('#skF_2', B_248, '#skF_1'('#skF_2', B_248, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_248) | B_248='#skF_6' | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_1180])).
% 4.27/1.72  tff(c_1191, plain, (![B_250]: (k3_orders_2('#skF_2', B_250, '#skF_1'('#skF_2', B_250, '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', B_250) | B_250='#skF_6' | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_1185])).
% 4.27/1.72  tff(c_1195, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | ~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_42, c_1191])).
% 4.27/1.72  tff(c_1202, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1195])).
% 4.27/1.72  tff(c_1203, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_1094, c_1202])).
% 4.27/1.72  tff(c_1208, plain, (![B_53]: (r2_hidden(B_53, '#skF_5') | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1203, c_26])).
% 4.27/1.72  tff(c_1215, plain, (![B_53]: (r2_hidden(B_53, '#skF_5') | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_42, c_1208])).
% 4.27/1.72  tff(c_1216, plain, (![B_53]: (r2_hidden(B_53, '#skF_5') | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_1215])).
% 4.27/1.72  tff(c_1218, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1216])).
% 4.27/1.72  tff(c_1234, plain, (~m1_orders_2('#skF_6', '#skF_2', '#skF_5') | '#skF_5'='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1105, c_1218])).
% 4.27/1.72  tff(c_1237, plain, ('#skF_5'='#skF_6' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_42, c_40, c_32, c_1234])).
% 4.27/1.72  tff(c_1239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1094, c_1237])).
% 4.27/1.72  tff(c_1241, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1216])).
% 4.27/1.72  tff(c_1206, plain, (![B_53]: (r2_orders_2('#skF_2', B_53, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1203, c_28])).
% 4.27/1.72  tff(c_1212, plain, (![B_53]: (r2_orders_2('#skF_2', B_53, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_42, c_1206])).
% 4.27/1.72  tff(c_1213, plain, (![B_53]: (r2_orders_2('#skF_2', B_53, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_53, '#skF_6') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_53, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_1212])).
% 4.27/1.72  tff(c_1345, plain, (![B_266]: (r2_orders_2('#skF_2', B_266, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~r2_hidden(B_266, '#skF_6') | ~m1_subset_1(B_266, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1241, c_1213])).
% 4.27/1.72  tff(c_1350, plain, (![B_38, B_266]: (~r1_orders_2('#skF_2', B_38, B_266) | r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~r2_hidden(B_266, '#skF_6') | ~m1_subset_1(B_266, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1345, c_20])).
% 4.27/1.72  tff(c_1372, plain, (![B_268, B_269]: (~r1_orders_2('#skF_2', B_268, B_269) | r2_orders_2('#skF_2', B_268, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(B_268, u1_struct_0('#skF_2')) | ~r2_hidden(B_269, '#skF_6') | ~m1_subset_1(B_269, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_1241, c_1350])).
% 4.27/1.72  tff(c_1376, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~r2_hidden('#skF_4', '#skF_6') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_63, c_1372])).
% 4.27/1.72  tff(c_1382, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_34, c_46, c_1376])).
% 4.27/1.72  tff(c_1298, plain, (![B_257, A_258, D_259, C_260]: (r2_hidden(B_257, k3_orders_2(A_258, D_259, C_260)) | ~r2_hidden(B_257, D_259) | ~r2_orders_2(A_258, B_257, C_260) | ~m1_subset_1(D_259, k1_zfmisc_1(u1_struct_0(A_258))) | ~m1_subset_1(C_260, u1_struct_0(A_258)) | ~m1_subset_1(B_257, u1_struct_0(A_258)) | ~l1_orders_2(A_258) | ~v5_orders_2(A_258) | ~v4_orders_2(A_258) | ~v3_orders_2(A_258) | v2_struct_0(A_258))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.27/1.72  tff(c_1302, plain, (![B_257, C_260]: (r2_hidden(B_257, k3_orders_2('#skF_2', '#skF_5', C_260)) | ~r2_hidden(B_257, '#skF_5') | ~r2_orders_2('#skF_2', B_257, C_260) | ~m1_subset_1(C_260, u1_struct_0('#skF_2')) | ~m1_subset_1(B_257, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_1298])).
% 4.27/1.72  tff(c_1309, plain, (![B_257, C_260]: (r2_hidden(B_257, k3_orders_2('#skF_2', '#skF_5', C_260)) | ~r2_hidden(B_257, '#skF_5') | ~r2_orders_2('#skF_2', B_257, C_260) | ~m1_subset_1(C_260, u1_struct_0('#skF_2')) | ~m1_subset_1(B_257, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_1302])).
% 4.27/1.72  tff(c_1324, plain, (![B_263, C_264]: (r2_hidden(B_263, k3_orders_2('#skF_2', '#skF_5', C_264)) | ~r2_hidden(B_263, '#skF_5') | ~r2_orders_2('#skF_2', B_263, C_264) | ~m1_subset_1(C_264, u1_struct_0('#skF_2')) | ~m1_subset_1(B_263, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_1309])).
% 4.27/1.72  tff(c_1331, plain, (![B_263]: (r2_hidden(B_263, '#skF_6') | ~r2_hidden(B_263, '#skF_5') | ~r2_orders_2('#skF_2', B_263, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_5', '#skF_6'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_263, u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1203, c_1324])).
% 4.27/1.72  tff(c_1341, plain, (![B_263]: (r2_hidden(B_263, '#skF_6') | ~r2_hidden(B_263, '#skF_5') | ~r2_orders_2('#skF_2', B_263, '#skF_1'('#skF_2', '#skF_5', '#skF_6')) | ~m1_subset_1(B_263, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1241, c_1331])).
% 4.27/1.72  tff(c_1385, plain, (r2_hidden('#skF_3', '#skF_6') | ~r2_hidden('#skF_3', '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1382, c_1341])).
% 4.27/1.72  tff(c_1392, plain, (r2_hidden('#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_36, c_1385])).
% 4.27/1.72  tff(c_1394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1392])).
% 4.27/1.72  tff(c_1395, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_495])).
% 4.27/1.72  tff(c_1415, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1395, c_32, c_1395, c_476])).
% 4.27/1.72  tff(c_1420, plain, (r2_hidden('#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1415, c_36])).
% 4.27/1.72  tff(c_1423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1420])).
% 4.27/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.27/1.72  
% 4.27/1.72  Inference rules
% 4.27/1.72  ----------------------
% 4.27/1.72  #Ref     : 0
% 4.27/1.72  #Sup     : 233
% 4.27/1.72  #Fact    : 0
% 4.27/1.72  #Define  : 0
% 4.27/1.72  #Split   : 33
% 4.27/1.72  #Chain   : 0
% 4.27/1.72  #Close   : 0
% 4.27/1.72  
% 4.27/1.72  Ordering : KBO
% 4.27/1.72  
% 4.27/1.72  Simplification rules
% 4.27/1.72  ----------------------
% 4.27/1.72  #Subsume      : 49
% 4.27/1.72  #Demod        : 535
% 4.27/1.72  #Tautology    : 57
% 4.27/1.72  #SimpNegUnit  : 96
% 4.27/1.72  #BackRed      : 32
% 4.27/1.72  
% 4.27/1.72  #Partial instantiations: 0
% 4.27/1.72  #Strategies tried      : 1
% 4.27/1.72  
% 4.27/1.72  Timing (in seconds)
% 4.27/1.72  ----------------------
% 4.27/1.73  Preprocessing        : 0.33
% 4.27/1.73  Parsing              : 0.18
% 4.27/1.73  CNF conversion       : 0.03
% 4.27/1.73  Main loop            : 0.57
% 4.27/1.73  Inferencing          : 0.20
% 4.27/1.73  Reduction            : 0.19
% 4.27/1.73  Demodulation         : 0.13
% 4.27/1.73  BG Simplification    : 0.03
% 4.27/1.73  Subsumption          : 0.12
% 4.27/1.73  Abstraction          : 0.03
% 4.27/1.73  MUC search           : 0.00
% 4.27/1.73  Cooper               : 0.00
% 4.27/1.73  Total                : 0.98
% 4.27/1.73  Index Insertion      : 0.00
% 4.27/1.73  Index Deletion       : 0.00
% 4.27/1.73  Index Matching       : 0.00
% 4.27/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
