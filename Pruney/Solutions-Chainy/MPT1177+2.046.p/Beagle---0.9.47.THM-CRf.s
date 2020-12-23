%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:01 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 425 expanded)
%              Number of leaves         :   39 ( 176 expanded)
%              Depth                    :   15
%              Number of atoms          :  300 (1948 expanded)
%              Number of equality atoms :   19 (  59 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(r2_wellord1,type,(
    r2_wellord1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_190,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => ! [C] :
                ( m2_orders_2(C,A,B)
               => ! [D] :
                    ( m2_orders_2(D,A,B)
                   => ( r2_xboole_0(C,D)
                    <=> m1_orders_2(C,A,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_orders_2(C,A,B)
         => ( v6_orders_2(C,A)
            & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_orders_2(C,A,B)
             => r1_tarski(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

tff(f_137,axiom,(
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
             => ~ ( B != k1_xboole_0
                  & m1_orders_2(B,A,C)
                  & m1_orders_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v6_orders_2(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
             => ( m2_orders_2(C,A,B)
              <=> ( C != k1_xboole_0
                  & r2_wellord1(u1_orders_2(A),C)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,C)
                       => k1_funct_1(B,k1_orders_2(A,k3_orders_2(A,C,D))) = D ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_165,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => ! [D] :
                  ( m2_orders_2(D,A,B)
                 => ( C != D
                   => ( m1_orders_2(C,A,D)
                    <=> ~ m1_orders_2(D,A,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_38,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_40,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_48,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_46,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_44,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_42,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_131,plain,(
    ! [C_91,A_92,B_93] :
      ( v6_orders_2(C_91,A_92)
      | ~ m2_orders_2(C_91,A_92,B_93)
      | ~ m1_orders_1(B_93,k1_orders_1(u1_struct_0(A_92)))
      | ~ l1_orders_2(A_92)
      | ~ v5_orders_2(A_92)
      | ~ v4_orders_2(A_92)
      | ~ v3_orders_2(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_133,plain,
    ( v6_orders_2('#skF_4','#skF_2')
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_131])).

tff(c_136,plain,
    ( v6_orders_2('#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_133])).

tff(c_137,plain,(
    v6_orders_2('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_136])).

tff(c_153,plain,(
    ! [C_96,A_97,B_98] :
      ( m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m2_orders_2(C_96,A_97,B_98)
      | ~ m1_orders_1(B_98,k1_orders_1(u1_struct_0(A_97)))
      | ~ l1_orders_2(A_97)
      | ~ v5_orders_2(A_97)
      | ~ v4_orders_2(A_97)
      | ~ v3_orders_2(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_155,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_153])).

tff(c_158,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_155])).

tff(c_159,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_158])).

tff(c_65,plain,(
    ! [A_78,B_79] :
      ( r2_xboole_0(A_78,B_79)
      | B_79 = A_78
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_60,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_64,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52])).

tff(c_79,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_65,c_64])).

tff(c_91,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_84,plain,(
    ! [C_80,B_81,A_82] :
      ( r1_tarski(C_80,B_81)
      | ~ m1_orders_2(C_80,A_82,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_86,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_84])).

tff(c_89,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_86])).

tff(c_90,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_89])).

tff(c_93,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_90])).

tff(c_36,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_107,plain,(
    ! [C_88,A_89,B_90] :
      ( m1_subset_1(C_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ m2_orders_2(C_88,A_89,B_90)
      | ~ m1_orders_1(B_90,k1_orders_1(u1_struct_0(A_89)))
      | ~ l1_orders_2(A_89)
      | ~ v5_orders_2(A_89)
      | ~ v4_orders_2(A_89)
      | ~ v3_orders_2(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_111,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_107])).

tff(c_118,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_111])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_93,c_118])).

tff(c_121,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_124,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_60])).

tff(c_161,plain,(
    ! [C_101,A_102,B_103] :
      ( ~ m1_orders_2(C_101,A_102,B_103)
      | ~ m1_orders_2(B_103,A_102,C_101)
      | k1_xboole_0 = B_103
      | ~ m1_subset_1(C_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_orders_2(A_102)
      | ~ v5_orders_2(A_102)
      | ~ v4_orders_2(A_102)
      | ~ v3_orders_2(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_163,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_124,c_161])).

tff(c_166,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_159,c_124,c_163])).

tff(c_167,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_166])).

tff(c_22,plain,(
    ! [A_7,B_19] :
      ( ~ m2_orders_2(k1_xboole_0,A_7,B_19)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ v6_orders_2(k1_xboole_0,A_7)
      | ~ m1_orders_1(B_19,k1_orders_1(u1_struct_0(A_7)))
      | ~ l1_orders_2(A_7)
      | ~ v5_orders_2(A_7)
      | ~ v4_orders_2(A_7)
      | ~ v3_orders_2(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_181,plain,(
    ! [A_107,B_108] :
      ( ~ m2_orders_2('#skF_4',A_107,B_108)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ v6_orders_2('#skF_4',A_107)
      | ~ m1_orders_1(B_108,k1_orders_1(u1_struct_0(A_107)))
      | ~ l1_orders_2(A_107)
      | ~ v5_orders_2(A_107)
      | ~ v4_orders_2(A_107)
      | ~ v3_orders_2(A_107)
      | v2_struct_0(A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_167,c_167,c_22])).

tff(c_183,plain,(
    ! [B_108] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_108)
      | ~ v6_orders_2('#skF_4','#skF_2')
      | ~ m1_orders_1(B_108,k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_159,c_181])).

tff(c_186,plain,(
    ! [B_108] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_108)
      | ~ m1_orders_1(B_108,k1_orders_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_137,c_183])).

tff(c_188,plain,(
    ! [B_109] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_109)
      | ~ m1_orders_1(B_109,k1_orders_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_186])).

tff(c_191,plain,(
    ~ m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_188])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_191])).

tff(c_196,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_203,plain,(
    ! [B_112,A_113] :
      ( ~ r2_xboole_0(B_112,A_113)
      | ~ r1_tarski(A_113,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_207,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_196,c_203])).

tff(c_243,plain,(
    ! [C_124,A_125,B_126] :
      ( m1_subset_1(C_124,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ m2_orders_2(C_124,A_125,B_126)
      | ~ m1_orders_1(B_126,k1_orders_1(u1_struct_0(A_125)))
      | ~ l1_orders_2(A_125)
      | ~ v5_orders_2(A_125)
      | ~ v4_orders_2(A_125)
      | ~ v3_orders_2(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_245,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_243])).

tff(c_250,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_245])).

tff(c_251,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_250])).

tff(c_8,plain,(
    ! [A_3] : ~ r2_xboole_0(A_3,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_197,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_271,plain,(
    ! [C_135,A_136,D_137,B_138] :
      ( m1_orders_2(C_135,A_136,D_137)
      | m1_orders_2(D_137,A_136,C_135)
      | D_137 = C_135
      | ~ m2_orders_2(D_137,A_136,B_138)
      | ~ m2_orders_2(C_135,A_136,B_138)
      | ~ m1_orders_1(B_138,k1_orders_1(u1_struct_0(A_136)))
      | ~ l1_orders_2(A_136)
      | ~ v5_orders_2(A_136)
      | ~ v4_orders_2(A_136)
      | ~ v3_orders_2(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_273,plain,(
    ! [C_135] :
      ( m1_orders_2(C_135,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_135)
      | C_135 = '#skF_4'
      | ~ m2_orders_2(C_135,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_271])).

tff(c_278,plain,(
    ! [C_135] :
      ( m1_orders_2(C_135,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_135)
      | C_135 = '#skF_4'
      | ~ m2_orders_2(C_135,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_273])).

tff(c_284,plain,(
    ! [C_139] :
      ( m1_orders_2(C_139,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_139)
      | C_139 = '#skF_4'
      | ~ m2_orders_2(C_139,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_278])).

tff(c_290,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | m1_orders_2('#skF_4','#skF_2','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_284])).

tff(c_295,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_290])).

tff(c_296,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_295])).

tff(c_303,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_196])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_303])).

tff(c_310,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_28,plain,(
    ! [C_39,B_37,A_33] :
      ( r1_tarski(C_39,B_37)
      | ~ m1_orders_2(C_39,A_33,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_orders_2(A_33)
      | ~ v5_orders_2(A_33)
      | ~ v4_orders_2(A_33)
      | ~ v3_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_318,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_310,c_28])).

tff(c_329,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_251,c_318])).

tff(c_331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_207,c_329])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:17:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.33  
% 2.53/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.33  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.53/1.33  
% 2.53/1.33  %Foreground sorts:
% 2.53/1.33  
% 2.53/1.33  
% 2.53/1.33  %Background operators:
% 2.53/1.33  
% 2.53/1.33  
% 2.53/1.33  %Foreground operators:
% 2.53/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.53/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.53/1.33  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.53/1.33  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.53/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.33  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.53/1.33  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.53/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.33  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.53/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.53/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.33  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.53/1.33  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.53/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.33  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.53/1.33  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.53/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.53/1.33  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.53/1.33  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.53/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.33  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.53/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.33  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.53/1.33  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.53/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.53/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.33  
% 2.69/1.35  tff(f_190, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.69/1.35  tff(f_93, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.69/1.35  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.69/1.35  tff(f_112, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.69/1.35  tff(f_137, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.69/1.35  tff(f_73, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_orders_2)).
% 2.69/1.35  tff(f_40, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.69/1.35  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 2.69/1.35  tff(f_165, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.69/1.35  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.69/1.35  tff(c_38, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.69/1.35  tff(c_40, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.69/1.35  tff(c_48, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.69/1.35  tff(c_46, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.69/1.35  tff(c_44, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.69/1.35  tff(c_42, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.69/1.35  tff(c_131, plain, (![C_91, A_92, B_93]: (v6_orders_2(C_91, A_92) | ~m2_orders_2(C_91, A_92, B_93) | ~m1_orders_1(B_93, k1_orders_1(u1_struct_0(A_92))) | ~l1_orders_2(A_92) | ~v5_orders_2(A_92) | ~v4_orders_2(A_92) | ~v3_orders_2(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.69/1.35  tff(c_133, plain, (v6_orders_2('#skF_4', '#skF_2') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_131])).
% 2.69/1.35  tff(c_136, plain, (v6_orders_2('#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_133])).
% 2.69/1.35  tff(c_137, plain, (v6_orders_2('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_136])).
% 2.69/1.35  tff(c_153, plain, (![C_96, A_97, B_98]: (m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~m2_orders_2(C_96, A_97, B_98) | ~m1_orders_1(B_98, k1_orders_1(u1_struct_0(A_97))) | ~l1_orders_2(A_97) | ~v5_orders_2(A_97) | ~v4_orders_2(A_97) | ~v3_orders_2(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.69/1.35  tff(c_155, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_153])).
% 2.69/1.35  tff(c_158, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_155])).
% 2.69/1.35  tff(c_159, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_158])).
% 2.69/1.35  tff(c_65, plain, (![A_78, B_79]: (r2_xboole_0(A_78, B_79) | B_79=A_78 | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.35  tff(c_58, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.69/1.35  tff(c_60, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitLeft, [status(thm)], [c_58])).
% 2.69/1.35  tff(c_52, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.69/1.35  tff(c_64, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_52])).
% 2.69/1.35  tff(c_79, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_65, c_64])).
% 2.69/1.35  tff(c_91, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_79])).
% 2.69/1.35  tff(c_84, plain, (![C_80, B_81, A_82]: (r1_tarski(C_80, B_81) | ~m1_orders_2(C_80, A_82, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.69/1.35  tff(c_86, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_84])).
% 2.69/1.35  tff(c_89, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_86])).
% 2.69/1.35  tff(c_90, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_89])).
% 2.69/1.35  tff(c_93, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_91, c_90])).
% 2.69/1.35  tff(c_36, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.69/1.35  tff(c_107, plain, (![C_88, A_89, B_90]: (m1_subset_1(C_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~m2_orders_2(C_88, A_89, B_90) | ~m1_orders_1(B_90, k1_orders_1(u1_struct_0(A_89))) | ~l1_orders_2(A_89) | ~v5_orders_2(A_89) | ~v4_orders_2(A_89) | ~v3_orders_2(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.69/1.35  tff(c_111, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_107])).
% 2.69/1.35  tff(c_118, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_111])).
% 2.69/1.35  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_93, c_118])).
% 2.69/1.35  tff(c_121, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_79])).
% 2.69/1.35  tff(c_124, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_60])).
% 2.69/1.35  tff(c_161, plain, (![C_101, A_102, B_103]: (~m1_orders_2(C_101, A_102, B_103) | ~m1_orders_2(B_103, A_102, C_101) | k1_xboole_0=B_103 | ~m1_subset_1(C_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_orders_2(A_102) | ~v5_orders_2(A_102) | ~v4_orders_2(A_102) | ~v3_orders_2(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.69/1.35  tff(c_163, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_124, c_161])).
% 2.69/1.35  tff(c_166, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_159, c_124, c_163])).
% 2.69/1.35  tff(c_167, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_166])).
% 2.69/1.35  tff(c_22, plain, (![A_7, B_19]: (~m2_orders_2(k1_xboole_0, A_7, B_19) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_7))) | ~v6_orders_2(k1_xboole_0, A_7) | ~m1_orders_1(B_19, k1_orders_1(u1_struct_0(A_7))) | ~l1_orders_2(A_7) | ~v5_orders_2(A_7) | ~v4_orders_2(A_7) | ~v3_orders_2(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.69/1.35  tff(c_181, plain, (![A_107, B_108]: (~m2_orders_2('#skF_4', A_107, B_108) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_107))) | ~v6_orders_2('#skF_4', A_107) | ~m1_orders_1(B_108, k1_orders_1(u1_struct_0(A_107))) | ~l1_orders_2(A_107) | ~v5_orders_2(A_107) | ~v4_orders_2(A_107) | ~v3_orders_2(A_107) | v2_struct_0(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_167, c_167, c_22])).
% 2.69/1.35  tff(c_183, plain, (![B_108]: (~m2_orders_2('#skF_4', '#skF_2', B_108) | ~v6_orders_2('#skF_4', '#skF_2') | ~m1_orders_1(B_108, k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_159, c_181])).
% 2.69/1.35  tff(c_186, plain, (![B_108]: (~m2_orders_2('#skF_4', '#skF_2', B_108) | ~m1_orders_1(B_108, k1_orders_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_137, c_183])).
% 2.69/1.35  tff(c_188, plain, (![B_109]: (~m2_orders_2('#skF_4', '#skF_2', B_109) | ~m1_orders_1(B_109, k1_orders_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_186])).
% 2.69/1.35  tff(c_191, plain, (~m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_188])).
% 2.69/1.35  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_191])).
% 2.69/1.35  tff(c_196, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 2.69/1.35  tff(c_203, plain, (![B_112, A_113]: (~r2_xboole_0(B_112, A_113) | ~r1_tarski(A_113, B_112))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.69/1.35  tff(c_207, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_196, c_203])).
% 2.69/1.35  tff(c_243, plain, (![C_124, A_125, B_126]: (m1_subset_1(C_124, k1_zfmisc_1(u1_struct_0(A_125))) | ~m2_orders_2(C_124, A_125, B_126) | ~m1_orders_1(B_126, k1_orders_1(u1_struct_0(A_125))) | ~l1_orders_2(A_125) | ~v5_orders_2(A_125) | ~v4_orders_2(A_125) | ~v3_orders_2(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.69/1.35  tff(c_245, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_243])).
% 2.69/1.35  tff(c_250, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_245])).
% 2.69/1.35  tff(c_251, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_250])).
% 2.69/1.35  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.35  tff(c_197, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 2.69/1.35  tff(c_271, plain, (![C_135, A_136, D_137, B_138]: (m1_orders_2(C_135, A_136, D_137) | m1_orders_2(D_137, A_136, C_135) | D_137=C_135 | ~m2_orders_2(D_137, A_136, B_138) | ~m2_orders_2(C_135, A_136, B_138) | ~m1_orders_1(B_138, k1_orders_1(u1_struct_0(A_136))) | ~l1_orders_2(A_136) | ~v5_orders_2(A_136) | ~v4_orders_2(A_136) | ~v3_orders_2(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.69/1.35  tff(c_273, plain, (![C_135]: (m1_orders_2(C_135, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_135) | C_135='#skF_4' | ~m2_orders_2(C_135, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_271])).
% 2.69/1.35  tff(c_278, plain, (![C_135]: (m1_orders_2(C_135, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_135) | C_135='#skF_4' | ~m2_orders_2(C_135, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_273])).
% 2.69/1.35  tff(c_284, plain, (![C_139]: (m1_orders_2(C_139, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_139) | C_139='#skF_4' | ~m2_orders_2(C_139, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_278])).
% 2.69/1.35  tff(c_290, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_36, c_284])).
% 2.69/1.35  tff(c_295, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_197, c_290])).
% 2.69/1.35  tff(c_296, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_295])).
% 2.69/1.35  tff(c_303, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_296, c_196])).
% 2.69/1.35  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_303])).
% 2.69/1.35  tff(c_310, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_295])).
% 2.69/1.35  tff(c_28, plain, (![C_39, B_37, A_33]: (r1_tarski(C_39, B_37) | ~m1_orders_2(C_39, A_33, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_orders_2(A_33) | ~v5_orders_2(A_33) | ~v4_orders_2(A_33) | ~v3_orders_2(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.69/1.35  tff(c_318, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_310, c_28])).
% 2.69/1.35  tff(c_329, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_251, c_318])).
% 2.69/1.35  tff(c_331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_207, c_329])).
% 2.69/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.35  
% 2.69/1.35  Inference rules
% 2.69/1.35  ----------------------
% 2.69/1.35  #Ref     : 0
% 2.69/1.35  #Sup     : 40
% 2.69/1.35  #Fact    : 0
% 2.69/1.35  #Define  : 0
% 2.69/1.35  #Split   : 3
% 2.69/1.35  #Chain   : 0
% 2.69/1.35  #Close   : 0
% 2.69/1.35  
% 2.69/1.35  Ordering : KBO
% 2.69/1.35  
% 2.69/1.35  Simplification rules
% 2.69/1.35  ----------------------
% 2.69/1.35  #Subsume      : 6
% 2.69/1.35  #Demod        : 143
% 2.69/1.35  #Tautology    : 18
% 2.69/1.35  #SimpNegUnit  : 25
% 2.69/1.35  #BackRed      : 13
% 2.69/1.35  
% 2.69/1.35  #Partial instantiations: 0
% 2.69/1.35  #Strategies tried      : 1
% 2.69/1.35  
% 2.69/1.35  Timing (in seconds)
% 2.69/1.35  ----------------------
% 2.69/1.36  Preprocessing        : 0.33
% 2.69/1.36  Parsing              : 0.18
% 2.69/1.36  CNF conversion       : 0.03
% 2.69/1.36  Main loop            : 0.25
% 2.69/1.36  Inferencing          : 0.09
% 2.69/1.36  Reduction            : 0.08
% 2.69/1.36  Demodulation         : 0.06
% 2.69/1.36  BG Simplification    : 0.02
% 2.69/1.36  Subsumption          : 0.04
% 2.69/1.36  Abstraction          : 0.01
% 2.69/1.36  MUC search           : 0.00
% 2.69/1.36  Cooper               : 0.00
% 2.69/1.36  Total                : 0.62
% 2.69/1.36  Index Insertion      : 0.00
% 2.69/1.36  Index Deletion       : 0.00
% 2.69/1.36  Index Matching       : 0.00
% 2.69/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
