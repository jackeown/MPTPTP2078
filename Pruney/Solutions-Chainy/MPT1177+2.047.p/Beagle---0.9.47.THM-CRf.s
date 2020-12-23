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
% DateTime   : Thu Dec  3 10:20:01 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 394 expanded)
%              Number of leaves         :   38 ( 162 expanded)
%              Depth                    :   16
%              Number of atoms          :  299 (1785 expanded)
%              Number of equality atoms :   21 (  74 expanded)
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

tff(f_188,negated_conjecture,(
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

tff(f_90,axiom,(
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

tff(f_109,axiom,(
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

tff(f_135,axiom,(
    ! [A] :
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

tff(f_70,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_163,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_38,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_40,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_48,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_46,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_44,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_42,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_178,plain,(
    ! [C_101,A_102,B_103] :
      ( v6_orders_2(C_101,A_102)
      | ~ m2_orders_2(C_101,A_102,B_103)
      | ~ m1_orders_1(B_103,k1_orders_1(u1_struct_0(A_102)))
      | ~ l1_orders_2(A_102)
      | ~ v5_orders_2(A_102)
      | ~ v4_orders_2(A_102)
      | ~ v3_orders_2(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_180,plain,
    ( v6_orders_2('#skF_4','#skF_2')
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_178])).

tff(c_183,plain,
    ( v6_orders_2('#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_180])).

tff(c_184,plain,(
    v6_orders_2('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_183])).

tff(c_65,plain,(
    ! [A_72,B_73] :
      ( r2_xboole_0(A_72,B_73)
      | B_73 = A_72
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_60,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_64,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52])).

tff(c_79,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_65,c_64])).

tff(c_85,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_88,plain,(
    ! [C_79,B_80,A_81] :
      ( r1_tarski(C_79,B_80)
      | ~ m1_orders_2(C_79,A_81,B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_orders_2(A_81)
      | ~ v5_orders_2(A_81)
      | ~ v4_orders_2(A_81)
      | ~ v3_orders_2(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_90,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_88])).

tff(c_93,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_90])).

tff(c_94,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_85,c_93])).

tff(c_36,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_108,plain,(
    ! [C_85,A_86,B_87] :
      ( m1_subset_1(C_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m2_orders_2(C_85,A_86,B_87)
      | ~ m1_orders_1(B_87,k1_orders_1(u1_struct_0(A_86)))
      | ~ l1_orders_2(A_86)
      | ~ v5_orders_2(A_86)
      | ~ v4_orders_2(A_86)
      | ~ v3_orders_2(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_112,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_108])).

tff(c_119,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_112])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_94,c_119])).

tff(c_122,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_125,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_60])).

tff(c_133,plain,(
    ! [B_88,A_89] :
      ( ~ m1_orders_2(B_88,A_89,B_88)
      | k1_xboole_0 = B_88
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_orders_2(A_89)
      | ~ v5_orders_2(A_89)
      | ~ v4_orders_2(A_89)
      | ~ v3_orders_2(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_135,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_125,c_133])).

tff(c_138,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_135])).

tff(c_139,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_138])).

tff(c_140,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_162,plain,(
    ! [C_98,A_99,B_100] :
      ( m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m2_orders_2(C_98,A_99,B_100)
      | ~ m1_orders_1(B_100,k1_orders_1(u1_struct_0(A_99)))
      | ~ l1_orders_2(A_99)
      | ~ v5_orders_2(A_99)
      | ~ v4_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_164,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_162])).

tff(c_167,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_164])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_140,c_167])).

tff(c_171,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_170,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_20,plain,(
    ! [A_5,B_17] :
      ( ~ m2_orders_2(k1_xboole_0,A_5,B_17)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ v6_orders_2(k1_xboole_0,A_5)
      | ~ m1_orders_1(B_17,k1_orders_1(u1_struct_0(A_5)))
      | ~ l1_orders_2(A_5)
      | ~ v5_orders_2(A_5)
      | ~ v4_orders_2(A_5)
      | ~ v3_orders_2(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_223,plain,(
    ! [A_115,B_116] :
      ( ~ m2_orders_2('#skF_4',A_115,B_116)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v6_orders_2('#skF_4',A_115)
      | ~ m1_orders_1(B_116,k1_orders_1(u1_struct_0(A_115)))
      | ~ l1_orders_2(A_115)
      | ~ v5_orders_2(A_115)
      | ~ v4_orders_2(A_115)
      | ~ v3_orders_2(A_115)
      | v2_struct_0(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_170,c_170,c_20])).

tff(c_225,plain,(
    ! [B_116] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_116)
      | ~ v6_orders_2('#skF_4','#skF_2')
      | ~ m1_orders_1(B_116,k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_171,c_223])).

tff(c_228,plain,(
    ! [B_116] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_116)
      | ~ m1_orders_1(B_116,k1_orders_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_184,c_225])).

tff(c_230,plain,(
    ! [B_117] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_117)
      | ~ m1_orders_1(B_117,k1_orders_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_228])).

tff(c_233,plain,(
    ~ m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_230])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_233])).

tff(c_238,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_242,plain,(
    ! [B_118,A_119] :
      ( ~ r2_xboole_0(B_118,A_119)
      | ~ r1_tarski(A_119,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_246,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_238,c_242])).

tff(c_287,plain,(
    ! [C_135,A_136,B_137] :
      ( m1_subset_1(C_135,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ m2_orders_2(C_135,A_136,B_137)
      | ~ m1_orders_1(B_137,k1_orders_1(u1_struct_0(A_136)))
      | ~ l1_orders_2(A_136)
      | ~ v5_orders_2(A_136)
      | ~ v4_orders_2(A_136)
      | ~ v3_orders_2(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_289,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_287])).

tff(c_294,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_289])).

tff(c_295,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_294])).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_241,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_52])).

tff(c_314,plain,(
    ! [C_143,A_144,D_145,B_146] :
      ( m1_orders_2(C_143,A_144,D_145)
      | m1_orders_2(D_145,A_144,C_143)
      | D_145 = C_143
      | ~ m2_orders_2(D_145,A_144,B_146)
      | ~ m2_orders_2(C_143,A_144,B_146)
      | ~ m1_orders_1(B_146,k1_orders_1(u1_struct_0(A_144)))
      | ~ l1_orders_2(A_144)
      | ~ v5_orders_2(A_144)
      | ~ v4_orders_2(A_144)
      | ~ v3_orders_2(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_316,plain,(
    ! [C_143] :
      ( m1_orders_2(C_143,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_143)
      | C_143 = '#skF_4'
      | ~ m2_orders_2(C_143,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_314])).

tff(c_321,plain,(
    ! [C_143] :
      ( m1_orders_2(C_143,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_143)
      | C_143 = '#skF_4'
      | ~ m2_orders_2(C_143,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_316])).

tff(c_327,plain,(
    ! [C_147] :
      ( m1_orders_2(C_147,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_147)
      | C_147 = '#skF_4'
      | ~ m2_orders_2(C_147,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_321])).

tff(c_333,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | m1_orders_2('#skF_4','#skF_2','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_327])).

tff(c_338,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_333])).

tff(c_339,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_338])).

tff(c_346,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_238])).

tff(c_352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_346])).

tff(c_353,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_338])).

tff(c_26,plain,(
    ! [C_37,B_35,A_31] :
      ( r1_tarski(C_37,B_35)
      | ~ m1_orders_2(C_37,A_31,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_orders_2(A_31)
      | ~ v5_orders_2(A_31)
      | ~ v4_orders_2(A_31)
      | ~ v3_orders_2(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_359,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_353,c_26])).

tff(c_366,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_295,c_359])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_246,c_366])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:56:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.66  
% 2.99/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.66  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.99/1.66  
% 2.99/1.66  %Foreground sorts:
% 2.99/1.66  
% 2.99/1.66  
% 2.99/1.66  %Background operators:
% 2.99/1.66  
% 2.99/1.66  
% 2.99/1.66  %Foreground operators:
% 2.99/1.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.99/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.99/1.66  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.99/1.66  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.99/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.66  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.99/1.66  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.99/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.66  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.99/1.66  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.66  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.66  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.66  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.99/1.66  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.99/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.66  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.99/1.66  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.99/1.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.99/1.66  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.99/1.66  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.99/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.66  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.99/1.66  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.66  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.99/1.66  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.99/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.99/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.66  
% 2.99/1.68  tff(f_188, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.99/1.68  tff(f_90, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.99/1.68  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.99/1.68  tff(f_109, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.99/1.68  tff(f_135, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k1_xboole_0) & m1_orders_2(B, A, B)) & ~(~m1_orders_2(B, A, B) & (B = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_orders_2)).
% 2.99/1.68  tff(f_70, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_orders_2)).
% 2.99/1.68  tff(f_37, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.99/1.68  tff(f_163, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.99/1.68  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.99/1.68  tff(c_38, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.99/1.68  tff(c_40, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.99/1.68  tff(c_48, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.99/1.68  tff(c_46, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.99/1.68  tff(c_44, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.99/1.68  tff(c_42, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.99/1.68  tff(c_178, plain, (![C_101, A_102, B_103]: (v6_orders_2(C_101, A_102) | ~m2_orders_2(C_101, A_102, B_103) | ~m1_orders_1(B_103, k1_orders_1(u1_struct_0(A_102))) | ~l1_orders_2(A_102) | ~v5_orders_2(A_102) | ~v4_orders_2(A_102) | ~v3_orders_2(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.99/1.68  tff(c_180, plain, (v6_orders_2('#skF_4', '#skF_2') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_178])).
% 2.99/1.68  tff(c_183, plain, (v6_orders_2('#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_180])).
% 2.99/1.68  tff(c_184, plain, (v6_orders_2('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_183])).
% 2.99/1.68  tff(c_65, plain, (![A_72, B_73]: (r2_xboole_0(A_72, B_73) | B_73=A_72 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.99/1.68  tff(c_58, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.99/1.68  tff(c_60, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitLeft, [status(thm)], [c_58])).
% 2.99/1.68  tff(c_52, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.99/1.68  tff(c_64, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_52])).
% 2.99/1.68  tff(c_79, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_65, c_64])).
% 2.99/1.68  tff(c_85, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_79])).
% 2.99/1.68  tff(c_88, plain, (![C_79, B_80, A_81]: (r1_tarski(C_79, B_80) | ~m1_orders_2(C_79, A_81, B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_orders_2(A_81) | ~v5_orders_2(A_81) | ~v4_orders_2(A_81) | ~v3_orders_2(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.99/1.68  tff(c_90, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_88])).
% 2.99/1.68  tff(c_93, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_90])).
% 2.99/1.68  tff(c_94, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_85, c_93])).
% 2.99/1.68  tff(c_36, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.99/1.68  tff(c_108, plain, (![C_85, A_86, B_87]: (m1_subset_1(C_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~m2_orders_2(C_85, A_86, B_87) | ~m1_orders_1(B_87, k1_orders_1(u1_struct_0(A_86))) | ~l1_orders_2(A_86) | ~v5_orders_2(A_86) | ~v4_orders_2(A_86) | ~v3_orders_2(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.99/1.68  tff(c_112, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_108])).
% 2.99/1.68  tff(c_119, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_112])).
% 2.99/1.68  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_94, c_119])).
% 2.99/1.68  tff(c_122, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_79])).
% 2.99/1.68  tff(c_125, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_60])).
% 2.99/1.68  tff(c_133, plain, (![B_88, A_89]: (~m1_orders_2(B_88, A_89, B_88) | k1_xboole_0=B_88 | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_orders_2(A_89) | ~v5_orders_2(A_89) | ~v4_orders_2(A_89) | ~v3_orders_2(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.99/1.68  tff(c_135, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_125, c_133])).
% 2.99/1.68  tff(c_138, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_135])).
% 2.99/1.68  tff(c_139, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_138])).
% 2.99/1.68  tff(c_140, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_139])).
% 2.99/1.68  tff(c_162, plain, (![C_98, A_99, B_100]: (m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~m2_orders_2(C_98, A_99, B_100) | ~m1_orders_1(B_100, k1_orders_1(u1_struct_0(A_99))) | ~l1_orders_2(A_99) | ~v5_orders_2(A_99) | ~v4_orders_2(A_99) | ~v3_orders_2(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.99/1.68  tff(c_164, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_162])).
% 2.99/1.68  tff(c_167, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_164])).
% 2.99/1.68  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_140, c_167])).
% 2.99/1.68  tff(c_171, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_139])).
% 2.99/1.68  tff(c_170, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_139])).
% 2.99/1.68  tff(c_20, plain, (![A_5, B_17]: (~m2_orders_2(k1_xboole_0, A_5, B_17) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_5))) | ~v6_orders_2(k1_xboole_0, A_5) | ~m1_orders_1(B_17, k1_orders_1(u1_struct_0(A_5))) | ~l1_orders_2(A_5) | ~v5_orders_2(A_5) | ~v4_orders_2(A_5) | ~v3_orders_2(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.99/1.68  tff(c_223, plain, (![A_115, B_116]: (~m2_orders_2('#skF_4', A_115, B_116) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_115))) | ~v6_orders_2('#skF_4', A_115) | ~m1_orders_1(B_116, k1_orders_1(u1_struct_0(A_115))) | ~l1_orders_2(A_115) | ~v5_orders_2(A_115) | ~v4_orders_2(A_115) | ~v3_orders_2(A_115) | v2_struct_0(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_170, c_170, c_20])).
% 2.99/1.68  tff(c_225, plain, (![B_116]: (~m2_orders_2('#skF_4', '#skF_2', B_116) | ~v6_orders_2('#skF_4', '#skF_2') | ~m1_orders_1(B_116, k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_171, c_223])).
% 2.99/1.68  tff(c_228, plain, (![B_116]: (~m2_orders_2('#skF_4', '#skF_2', B_116) | ~m1_orders_1(B_116, k1_orders_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_184, c_225])).
% 2.99/1.68  tff(c_230, plain, (![B_117]: (~m2_orders_2('#skF_4', '#skF_2', B_117) | ~m1_orders_1(B_117, k1_orders_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_228])).
% 2.99/1.68  tff(c_233, plain, (~m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_230])).
% 2.99/1.68  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_233])).
% 2.99/1.68  tff(c_238, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 2.99/1.68  tff(c_242, plain, (![B_118, A_119]: (~r2_xboole_0(B_118, A_119) | ~r1_tarski(A_119, B_118))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.68  tff(c_246, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_238, c_242])).
% 2.99/1.68  tff(c_287, plain, (![C_135, A_136, B_137]: (m1_subset_1(C_135, k1_zfmisc_1(u1_struct_0(A_136))) | ~m2_orders_2(C_135, A_136, B_137) | ~m1_orders_1(B_137, k1_orders_1(u1_struct_0(A_136))) | ~l1_orders_2(A_136) | ~v5_orders_2(A_136) | ~v4_orders_2(A_136) | ~v3_orders_2(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.99/1.68  tff(c_289, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_287])).
% 2.99/1.68  tff(c_294, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_289])).
% 2.99/1.68  tff(c_295, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_294])).
% 2.99/1.68  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.99/1.68  tff(c_241, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_52])).
% 2.99/1.68  tff(c_314, plain, (![C_143, A_144, D_145, B_146]: (m1_orders_2(C_143, A_144, D_145) | m1_orders_2(D_145, A_144, C_143) | D_145=C_143 | ~m2_orders_2(D_145, A_144, B_146) | ~m2_orders_2(C_143, A_144, B_146) | ~m1_orders_1(B_146, k1_orders_1(u1_struct_0(A_144))) | ~l1_orders_2(A_144) | ~v5_orders_2(A_144) | ~v4_orders_2(A_144) | ~v3_orders_2(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.99/1.68  tff(c_316, plain, (![C_143]: (m1_orders_2(C_143, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_143) | C_143='#skF_4' | ~m2_orders_2(C_143, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_314])).
% 2.99/1.68  tff(c_321, plain, (![C_143]: (m1_orders_2(C_143, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_143) | C_143='#skF_4' | ~m2_orders_2(C_143, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_316])).
% 2.99/1.68  tff(c_327, plain, (![C_147]: (m1_orders_2(C_147, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_147) | C_147='#skF_4' | ~m2_orders_2(C_147, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_321])).
% 2.99/1.68  tff(c_333, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_36, c_327])).
% 2.99/1.68  tff(c_338, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_241, c_333])).
% 2.99/1.68  tff(c_339, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_338])).
% 2.99/1.68  tff(c_346, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_238])).
% 2.99/1.68  tff(c_352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_346])).
% 2.99/1.68  tff(c_353, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_338])).
% 2.99/1.68  tff(c_26, plain, (![C_37, B_35, A_31]: (r1_tarski(C_37, B_35) | ~m1_orders_2(C_37, A_31, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_orders_2(A_31) | ~v5_orders_2(A_31) | ~v4_orders_2(A_31) | ~v3_orders_2(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.99/1.68  tff(c_359, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_353, c_26])).
% 2.99/1.68  tff(c_366, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_295, c_359])).
% 2.99/1.68  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_246, c_366])).
% 2.99/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.68  
% 2.99/1.68  Inference rules
% 2.99/1.68  ----------------------
% 2.99/1.68  #Ref     : 0
% 2.99/1.68  #Sup     : 44
% 2.99/1.68  #Fact    : 0
% 2.99/1.68  #Define  : 0
% 2.99/1.68  #Split   : 4
% 2.99/1.68  #Chain   : 0
% 2.99/1.68  #Close   : 0
% 2.99/1.68  
% 2.99/1.68  Ordering : KBO
% 2.99/1.68  
% 2.99/1.68  Simplification rules
% 2.99/1.68  ----------------------
% 2.99/1.68  #Subsume      : 5
% 2.99/1.68  #Demod        : 156
% 2.99/1.68  #Tautology    : 21
% 2.99/1.68  #SimpNegUnit  : 27
% 2.99/1.68  #BackRed      : 13
% 2.99/1.68  
% 2.99/1.68  #Partial instantiations: 0
% 2.99/1.68  #Strategies tried      : 1
% 2.99/1.68  
% 2.99/1.68  Timing (in seconds)
% 2.99/1.68  ----------------------
% 2.99/1.68  Preprocessing        : 0.48
% 2.99/1.68  Parsing              : 0.28
% 2.99/1.68  CNF conversion       : 0.04
% 2.99/1.68  Main loop            : 0.27
% 2.99/1.68  Inferencing          : 0.10
% 2.99/1.68  Reduction            : 0.09
% 2.99/1.68  Demodulation         : 0.07
% 2.99/1.68  BG Simplification    : 0.02
% 2.99/1.68  Subsumption          : 0.05
% 2.99/1.68  Abstraction          : 0.01
% 2.99/1.68  MUC search           : 0.00
% 2.99/1.68  Cooper               : 0.00
% 2.99/1.68  Total                : 0.80
% 2.99/1.68  Index Insertion      : 0.00
% 2.99/1.68  Index Deletion       : 0.00
% 2.99/1.68  Index Matching       : 0.00
% 2.99/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
