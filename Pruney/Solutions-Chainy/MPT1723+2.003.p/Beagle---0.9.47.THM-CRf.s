%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:45 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 241 expanded)
%              Number of leaves         :   21 ( 102 expanded)
%              Depth                    :   12
%              Number of atoms          :  359 (1537 expanded)
%              Number of equality atoms :   32 (  36 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > k1_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( ~ r1_tsep_1(B,C)
                     => ( ( m1_pre_topc(B,D)
                         => m1_pre_topc(k2_tsep_1(A,B,C),k2_tsep_1(A,D,C)) )
                        & ( m1_pre_topc(C,D)
                         => m1_pre_topc(k2_tsep_1(A,B,C),k2_tsep_1(A,B,D)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tmap_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( m1_pre_topc(B,C)
              <=> k1_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( ~ v2_struct_0(E)
                        & m1_pre_topc(E,A) )
                     => ( ( m1_pre_topc(B,D)
                          & m1_pre_topc(C,E) )
                       => ( r1_tsep_1(B,C)
                          | m1_pre_topc(k2_tsep_1(A,B,C),k2_tsep_1(A,D,E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tmap_1)).

tff(c_18,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_16,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_380,plain,(
    ! [A_85,B_86] :
      ( k1_tsep_1(A_85,B_86,B_86) = g1_pre_topc(u1_struct_0(B_86),u1_pre_topc(B_86))
      | ~ m1_pre_topc(B_86,A_85)
      | v2_struct_0(B_86)
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_390,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_380])).

tff(c_406,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_390])).

tff(c_407,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_18,c_406])).

tff(c_456,plain,(
    ! [B_90,C_91,A_92] :
      ( m1_pre_topc(B_90,C_91)
      | k1_tsep_1(A_92,B_90,C_91) != g1_pre_topc(u1_struct_0(C_91),u1_pre_topc(C_91))
      | ~ m1_pre_topc(C_91,A_92)
      | v2_struct_0(C_91)
      | ~ m1_pre_topc(B_90,A_92)
      | v2_struct_0(B_90)
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_460,plain,(
    ! [B_90,A_92] :
      ( m1_pre_topc(B_90,'#skF_3')
      | k1_tsep_1(A_92,B_90,'#skF_3') != k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_92)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_90,A_92)
      | v2_struct_0(B_90)
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_456])).

tff(c_538,plain,(
    ! [B_103,A_104] :
      ( m1_pre_topc(B_103,'#skF_3')
      | k1_tsep_1(A_104,B_103,'#skF_3') != k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_104)
      | ~ m1_pre_topc(B_103,A_104)
      | v2_struct_0(B_103)
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_460])).

tff(c_542,plain,(
    ! [B_103] :
      ( m1_pre_topc(B_103,'#skF_3')
      | k1_tsep_1('#skF_1',B_103,'#skF_3') != k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc(B_103,'#skF_1')
      | v2_struct_0(B_103)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_538])).

tff(c_547,plain,(
    ! [B_103] :
      ( m1_pre_topc(B_103,'#skF_3')
      | k1_tsep_1('#skF_1',B_103,'#skF_3') != k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc(B_103,'#skF_1')
      | v2_struct_0(B_103)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_542])).

tff(c_549,plain,(
    ! [B_105] :
      ( m1_pre_topc(B_105,'#skF_3')
      | k1_tsep_1('#skF_1',B_105,'#skF_3') != k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc(B_105,'#skF_1')
      | v2_struct_0(B_105) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_547])).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_14,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_10,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_20,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_12,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_40,plain,(
    ! [A_53,B_54] :
      ( k1_tsep_1(A_53,B_54,B_54) = g1_pre_topc(u1_struct_0(B_54),u1_pre_topc(B_54))
      | ~ m1_pre_topc(B_54,A_53)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_44,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_40])).

tff(c_54,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_44])).

tff(c_55,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_22,c_54])).

tff(c_116,plain,(
    ! [B_59,C_60,A_61] :
      ( m1_pre_topc(B_59,C_60)
      | k1_tsep_1(A_61,B_59,C_60) != g1_pre_topc(u1_struct_0(C_60),u1_pre_topc(C_60))
      | ~ m1_pre_topc(C_60,A_61)
      | v2_struct_0(C_60)
      | ~ m1_pre_topc(B_59,A_61)
      | v2_struct_0(B_59)
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_122,plain,(
    ! [B_59,A_61] :
      ( m1_pre_topc(B_59,'#skF_2')
      | k1_tsep_1(A_61,B_59,'#skF_2') != k1_tsep_1('#skF_1','#skF_2','#skF_2')
      | ~ m1_pre_topc('#skF_2',A_61)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_59,A_61)
      | v2_struct_0(B_59)
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_116])).

tff(c_308,plain,(
    ! [B_82,A_83] :
      ( m1_pre_topc(B_82,'#skF_2')
      | k1_tsep_1(A_83,B_82,'#skF_2') != k1_tsep_1('#skF_1','#skF_2','#skF_2')
      | ~ m1_pre_topc('#skF_2',A_83)
      | ~ m1_pre_topc(B_82,A_83)
      | v2_struct_0(B_82)
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_122])).

tff(c_313,plain,(
    ! [B_82] :
      ( m1_pre_topc(B_82,'#skF_2')
      | k1_tsep_1('#skF_1',B_82,'#skF_2') != k1_tsep_1('#skF_1','#skF_2','#skF_2')
      | ~ m1_pre_topc(B_82,'#skF_1')
      | v2_struct_0(B_82)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_308])).

tff(c_320,plain,(
    ! [B_82] :
      ( m1_pre_topc(B_82,'#skF_2')
      | k1_tsep_1('#skF_1',B_82,'#skF_2') != k1_tsep_1('#skF_1','#skF_2','#skF_2')
      | ~ m1_pre_topc(B_82,'#skF_1')
      | v2_struct_0(B_82)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_313])).

tff(c_322,plain,(
    ! [B_84] :
      ( m1_pre_topc(B_84,'#skF_2')
      | k1_tsep_1('#skF_1',B_84,'#skF_2') != k1_tsep_1('#skF_1','#skF_2','#skF_2')
      | ~ m1_pre_topc(B_84,'#skF_1')
      | v2_struct_0(B_84) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_320])).

tff(c_36,plain,
    ( m1_pre_topc('#skF_2','#skF_4')
    | m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_37,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_203,plain,(
    ! [B_68,E_70,D_72,C_69,A_71] :
      ( m1_pre_topc(k2_tsep_1(A_71,B_68,C_69),k2_tsep_1(A_71,D_72,E_70))
      | r1_tsep_1(B_68,C_69)
      | ~ m1_pre_topc(C_69,E_70)
      | ~ m1_pre_topc(B_68,D_72)
      | ~ m1_pre_topc(E_70,A_71)
      | v2_struct_0(E_70)
      | ~ m1_pre_topc(D_72,A_71)
      | v2_struct_0(D_72)
      | ~ m1_pre_topc(C_69,A_71)
      | v2_struct_0(C_69)
      | ~ m1_pre_topc(B_68,A_71)
      | v2_struct_0(B_68)
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,
    ( m1_pre_topc('#skF_2','#skF_4')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_39,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_210,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_203,c_39])).

tff(c_215,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_16,c_12,c_37,c_210])).

tff(c_216,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_22,c_18,c_14,c_10,c_215])).

tff(c_335,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_322,c_216])).

tff(c_370,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_335])).

tff(c_372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_370])).

tff(c_373,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_524,plain,(
    ! [C_99,B_98,E_100,A_101,D_102] :
      ( m1_pre_topc(k2_tsep_1(A_101,B_98,C_99),k2_tsep_1(A_101,D_102,E_100))
      | r1_tsep_1(B_98,C_99)
      | ~ m1_pre_topc(C_99,E_100)
      | ~ m1_pre_topc(B_98,D_102)
      | ~ m1_pre_topc(E_100,A_101)
      | v2_struct_0(E_100)
      | ~ m1_pre_topc(D_102,A_101)
      | v2_struct_0(D_102)
      | ~ m1_pre_topc(C_99,A_101)
      | v2_struct_0(C_99)
      | ~ m1_pre_topc(B_98,A_101)
      | v2_struct_0(B_98)
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_4','#skF_3'))
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_375,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_374,plain,(
    m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_374])).

tff(c_377,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_531,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_524,c_377])).

tff(c_536,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_16,c_12,c_373,c_531])).

tff(c_537,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_22,c_18,c_14,c_10,c_536])).

tff(c_555,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_549,c_537])).

tff(c_583,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_555])).

tff(c_585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_583])).

tff(c_587,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_590,plain,(
    ! [A_106,B_107] :
      ( k1_tsep_1(A_106,B_107,B_107) = g1_pre_topc(u1_struct_0(B_107),u1_pre_topc(B_107))
      | ~ m1_pre_topc(B_107,A_106)
      | v2_struct_0(B_107)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_596,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_590])).

tff(c_608,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_596])).

tff(c_609,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_18,c_608])).

tff(c_628,plain,(
    ! [B_108,C_109,A_110] :
      ( m1_pre_topc(B_108,C_109)
      | k1_tsep_1(A_110,B_108,C_109) != g1_pre_topc(u1_struct_0(C_109),u1_pre_topc(C_109))
      | ~ m1_pre_topc(C_109,A_110)
      | v2_struct_0(C_109)
      | ~ m1_pre_topc(B_108,A_110)
      | v2_struct_0(B_108)
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_630,plain,(
    ! [B_108,A_110] :
      ( m1_pre_topc(B_108,'#skF_3')
      | k1_tsep_1(A_110,B_108,'#skF_3') != k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_110)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_108,A_110)
      | v2_struct_0(B_108)
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_628])).

tff(c_638,plain,(
    ! [B_111,A_112] :
      ( m1_pre_topc(B_111,'#skF_3')
      | k1_tsep_1(A_112,B_111,'#skF_3') != k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_112)
      | ~ m1_pre_topc(B_111,A_112)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_630])).

tff(c_640,plain,(
    ! [B_111] :
      ( m1_pre_topc(B_111,'#skF_3')
      | k1_tsep_1('#skF_1',B_111,'#skF_3') != k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc(B_111,'#skF_1')
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_638])).

tff(c_643,plain,(
    ! [B_111] :
      ( m1_pre_topc(B_111,'#skF_3')
      | k1_tsep_1('#skF_1',B_111,'#skF_3') != k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc(B_111,'#skF_1')
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_640])).

tff(c_644,plain,(
    ! [B_111] :
      ( m1_pre_topc(B_111,'#skF_3')
      | k1_tsep_1('#skF_1',B_111,'#skF_3') != k1_tsep_1('#skF_1','#skF_3','#skF_3')
      | ~ m1_pre_topc(B_111,'#skF_1')
      | v2_struct_0(B_111) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_643])).

tff(c_586,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_799,plain,(
    ! [D_127,E_125,A_126,B_123,C_124] :
      ( m1_pre_topc(k2_tsep_1(A_126,B_123,C_124),k2_tsep_1(A_126,D_127,E_125))
      | r1_tsep_1(B_123,C_124)
      | ~ m1_pre_topc(C_124,E_125)
      | ~ m1_pre_topc(B_123,D_127)
      | ~ m1_pre_topc(E_125,A_126)
      | v2_struct_0(E_125)
      | ~ m1_pre_topc(D_127,A_126)
      | v2_struct_0(D_127)
      | ~ m1_pre_topc(C_124,A_126)
      | v2_struct_0(C_124)
      | ~ m1_pre_topc(B_123,A_126)
      | v2_struct_0(B_123)
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_4','#skF_3'))
    | m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_588,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_806,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_799,c_588])).

tff(c_811,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_16,c_12,c_586,c_806])).

tff(c_812,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_22,c_18,c_14,c_10,c_811])).

tff(c_815,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_644,c_812])).

tff(c_818,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_815])).

tff(c_820,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_818])).

tff(c_821,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_587,c_821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.47  
% 3.29/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.47  %$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > k1_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.29/1.47  
% 3.29/1.47  %Foreground sorts:
% 3.29/1.47  
% 3.29/1.47  
% 3.29/1.47  %Background operators:
% 3.29/1.47  
% 3.29/1.47  
% 3.29/1.47  %Foreground operators:
% 3.29/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.29/1.47  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.29/1.47  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.29/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.47  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.29/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.29/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.29/1.47  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 3.29/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.29/1.47  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.29/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.29/1.47  
% 3.29/1.49  tff(f_139, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(B, C) => ((m1_pre_topc(B, D) => m1_pre_topc(k2_tsep_1(A, B, C), k2_tsep_1(A, D, C))) & (m1_pre_topc(C, D) => m1_pre_topc(k2_tsep_1(A, B, C), k2_tsep_1(A, B, D))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tmap_1)).
% 3.29/1.49  tff(f_63, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 3.29/1.49  tff(f_48, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) <=> (k1_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tsep_1)).
% 3.29/1.49  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, E)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), k2_tsep_1(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tmap_1)).
% 3.29/1.49  tff(c_18, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.29/1.49  tff(c_16, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.29/1.49  tff(c_28, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.29/1.49  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.29/1.49  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.29/1.49  tff(c_380, plain, (![A_85, B_86]: (k1_tsep_1(A_85, B_86, B_86)=g1_pre_topc(u1_struct_0(B_86), u1_pre_topc(B_86)) | ~m1_pre_topc(B_86, A_85) | v2_struct_0(B_86) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.29/1.49  tff(c_390, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_380])).
% 3.29/1.49  tff(c_406, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_390])).
% 3.29/1.49  tff(c_407, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_18, c_406])).
% 3.29/1.49  tff(c_456, plain, (![B_90, C_91, A_92]: (m1_pre_topc(B_90, C_91) | k1_tsep_1(A_92, B_90, C_91)!=g1_pre_topc(u1_struct_0(C_91), u1_pre_topc(C_91)) | ~m1_pre_topc(C_91, A_92) | v2_struct_0(C_91) | ~m1_pre_topc(B_90, A_92) | v2_struct_0(B_90) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.29/1.49  tff(c_460, plain, (![B_90, A_92]: (m1_pre_topc(B_90, '#skF_3') | k1_tsep_1(A_92, B_90, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_92) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_90, A_92) | v2_struct_0(B_90) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(superposition, [status(thm), theory('equality')], [c_407, c_456])).
% 3.29/1.49  tff(c_538, plain, (![B_103, A_104]: (m1_pre_topc(B_103, '#skF_3') | k1_tsep_1(A_104, B_103, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_104) | ~m1_pre_topc(B_103, A_104) | v2_struct_0(B_103) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104) | v2_struct_0(A_104))), inference(negUnitSimplification, [status(thm)], [c_18, c_460])).
% 3.29/1.49  tff(c_542, plain, (![B_103]: (m1_pre_topc(B_103, '#skF_3') | k1_tsep_1('#skF_1', B_103, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc(B_103, '#skF_1') | v2_struct_0(B_103) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_538])).
% 3.29/1.49  tff(c_547, plain, (![B_103]: (m1_pre_topc(B_103, '#skF_3') | k1_tsep_1('#skF_1', B_103, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc(B_103, '#skF_1') | v2_struct_0(B_103) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_542])).
% 3.29/1.49  tff(c_549, plain, (![B_105]: (m1_pre_topc(B_105, '#skF_3') | k1_tsep_1('#skF_1', B_105, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc(B_105, '#skF_1') | v2_struct_0(B_105))), inference(negUnitSimplification, [status(thm)], [c_28, c_547])).
% 3.29/1.49  tff(c_22, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.29/1.49  tff(c_14, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.29/1.49  tff(c_10, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.29/1.49  tff(c_20, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.29/1.49  tff(c_12, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.29/1.49  tff(c_40, plain, (![A_53, B_54]: (k1_tsep_1(A_53, B_54, B_54)=g1_pre_topc(u1_struct_0(B_54), u1_pre_topc(B_54)) | ~m1_pre_topc(B_54, A_53) | v2_struct_0(B_54) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.29/1.49  tff(c_44, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_40])).
% 3.29/1.49  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_44])).
% 3.29/1.49  tff(c_55, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28, c_22, c_54])).
% 3.29/1.49  tff(c_116, plain, (![B_59, C_60, A_61]: (m1_pre_topc(B_59, C_60) | k1_tsep_1(A_61, B_59, C_60)!=g1_pre_topc(u1_struct_0(C_60), u1_pre_topc(C_60)) | ~m1_pre_topc(C_60, A_61) | v2_struct_0(C_60) | ~m1_pre_topc(B_59, A_61) | v2_struct_0(B_59) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.29/1.49  tff(c_122, plain, (![B_59, A_61]: (m1_pre_topc(B_59, '#skF_2') | k1_tsep_1(A_61, B_59, '#skF_2')!=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', A_61) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_59, A_61) | v2_struct_0(B_59) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61) | v2_struct_0(A_61))), inference(superposition, [status(thm), theory('equality')], [c_55, c_116])).
% 3.29/1.49  tff(c_308, plain, (![B_82, A_83]: (m1_pre_topc(B_82, '#skF_2') | k1_tsep_1(A_83, B_82, '#skF_2')!=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', A_83) | ~m1_pre_topc(B_82, A_83) | v2_struct_0(B_82) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(negUnitSimplification, [status(thm)], [c_22, c_122])).
% 3.29/1.49  tff(c_313, plain, (![B_82]: (m1_pre_topc(B_82, '#skF_2') | k1_tsep_1('#skF_1', B_82, '#skF_2')!=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~m1_pre_topc(B_82, '#skF_1') | v2_struct_0(B_82) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_308])).
% 3.29/1.49  tff(c_320, plain, (![B_82]: (m1_pre_topc(B_82, '#skF_2') | k1_tsep_1('#skF_1', B_82, '#skF_2')!=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~m1_pre_topc(B_82, '#skF_1') | v2_struct_0(B_82) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_313])).
% 3.29/1.49  tff(c_322, plain, (![B_84]: (m1_pre_topc(B_84, '#skF_2') | k1_tsep_1('#skF_1', B_84, '#skF_2')!=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~m1_pre_topc(B_84, '#skF_1') | v2_struct_0(B_84))), inference(negUnitSimplification, [status(thm)], [c_28, c_320])).
% 3.29/1.49  tff(c_36, plain, (m1_pre_topc('#skF_2', '#skF_4') | m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.29/1.49  tff(c_37, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_36])).
% 3.29/1.49  tff(c_203, plain, (![B_68, E_70, D_72, C_69, A_71]: (m1_pre_topc(k2_tsep_1(A_71, B_68, C_69), k2_tsep_1(A_71, D_72, E_70)) | r1_tsep_1(B_68, C_69) | ~m1_pre_topc(C_69, E_70) | ~m1_pre_topc(B_68, D_72) | ~m1_pre_topc(E_70, A_71) | v2_struct_0(E_70) | ~m1_pre_topc(D_72, A_71) | v2_struct_0(D_72) | ~m1_pre_topc(C_69, A_71) | v2_struct_0(C_69) | ~m1_pre_topc(B_68, A_71) | v2_struct_0(B_68) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.29/1.49  tff(c_32, plain, (m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.29/1.49  tff(c_39, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_32])).
% 3.29/1.49  tff(c_210, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_203, c_39])).
% 3.29/1.49  tff(c_215, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_16, c_12, c_37, c_210])).
% 3.29/1.49  tff(c_216, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28, c_22, c_18, c_14, c_10, c_215])).
% 3.29/1.49  tff(c_335, plain, (~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_322, c_216])).
% 3.29/1.49  tff(c_370, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_335])).
% 3.29/1.49  tff(c_372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_370])).
% 3.29/1.49  tff(c_373, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 3.29/1.49  tff(c_524, plain, (![C_99, B_98, E_100, A_101, D_102]: (m1_pre_topc(k2_tsep_1(A_101, B_98, C_99), k2_tsep_1(A_101, D_102, E_100)) | r1_tsep_1(B_98, C_99) | ~m1_pre_topc(C_99, E_100) | ~m1_pre_topc(B_98, D_102) | ~m1_pre_topc(E_100, A_101) | v2_struct_0(E_100) | ~m1_pre_topc(D_102, A_101) | v2_struct_0(D_102) | ~m1_pre_topc(C_99, A_101) | v2_struct_0(C_99) | ~m1_pre_topc(B_98, A_101) | v2_struct_0(B_98) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.29/1.49  tff(c_30, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.29/1.49  tff(c_375, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_30])).
% 3.29/1.49  tff(c_374, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_32])).
% 3.29/1.49  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_375, c_374])).
% 3.29/1.49  tff(c_377, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_30])).
% 3.29/1.49  tff(c_531, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_524, c_377])).
% 3.29/1.49  tff(c_536, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_16, c_12, c_373, c_531])).
% 3.29/1.49  tff(c_537, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_22, c_18, c_14, c_10, c_536])).
% 3.29/1.49  tff(c_555, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_549, c_537])).
% 3.29/1.49  tff(c_583, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_555])).
% 3.29/1.49  tff(c_585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_583])).
% 3.29/1.49  tff(c_587, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 3.29/1.49  tff(c_590, plain, (![A_106, B_107]: (k1_tsep_1(A_106, B_107, B_107)=g1_pre_topc(u1_struct_0(B_107), u1_pre_topc(B_107)) | ~m1_pre_topc(B_107, A_106) | v2_struct_0(B_107) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.29/1.49  tff(c_596, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_590])).
% 3.29/1.49  tff(c_608, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_596])).
% 3.29/1.49  tff(c_609, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_18, c_608])).
% 3.29/1.49  tff(c_628, plain, (![B_108, C_109, A_110]: (m1_pre_topc(B_108, C_109) | k1_tsep_1(A_110, B_108, C_109)!=g1_pre_topc(u1_struct_0(C_109), u1_pre_topc(C_109)) | ~m1_pre_topc(C_109, A_110) | v2_struct_0(C_109) | ~m1_pre_topc(B_108, A_110) | v2_struct_0(B_108) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.29/1.49  tff(c_630, plain, (![B_108, A_110]: (m1_pre_topc(B_108, '#skF_3') | k1_tsep_1(A_110, B_108, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_110) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_108, A_110) | v2_struct_0(B_108) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(superposition, [status(thm), theory('equality')], [c_609, c_628])).
% 3.29/1.49  tff(c_638, plain, (![B_111, A_112]: (m1_pre_topc(B_111, '#skF_3') | k1_tsep_1(A_112, B_111, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_112) | ~m1_pre_topc(B_111, A_112) | v2_struct_0(B_111) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112) | v2_struct_0(A_112))), inference(negUnitSimplification, [status(thm)], [c_18, c_630])).
% 3.29/1.49  tff(c_640, plain, (![B_111]: (m1_pre_topc(B_111, '#skF_3') | k1_tsep_1('#skF_1', B_111, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc(B_111, '#skF_1') | v2_struct_0(B_111) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_638])).
% 3.29/1.49  tff(c_643, plain, (![B_111]: (m1_pre_topc(B_111, '#skF_3') | k1_tsep_1('#skF_1', B_111, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc(B_111, '#skF_1') | v2_struct_0(B_111) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_640])).
% 3.29/1.49  tff(c_644, plain, (![B_111]: (m1_pre_topc(B_111, '#skF_3') | k1_tsep_1('#skF_1', B_111, '#skF_3')!=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | ~m1_pre_topc(B_111, '#skF_1') | v2_struct_0(B_111))), inference(negUnitSimplification, [status(thm)], [c_28, c_643])).
% 3.29/1.49  tff(c_586, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 3.29/1.49  tff(c_799, plain, (![D_127, E_125, A_126, B_123, C_124]: (m1_pre_topc(k2_tsep_1(A_126, B_123, C_124), k2_tsep_1(A_126, D_127, E_125)) | r1_tsep_1(B_123, C_124) | ~m1_pre_topc(C_124, E_125) | ~m1_pre_topc(B_123, D_127) | ~m1_pre_topc(E_125, A_126) | v2_struct_0(E_125) | ~m1_pre_topc(D_127, A_126) | v2_struct_0(D_127) | ~m1_pre_topc(C_124, A_126) | v2_struct_0(C_124) | ~m1_pre_topc(B_123, A_126) | v2_struct_0(B_123) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.29/1.49  tff(c_34, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_4', '#skF_3')) | m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.29/1.49  tff(c_588, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_34])).
% 3.29/1.49  tff(c_806, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_799, c_588])).
% 3.29/1.49  tff(c_811, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_16, c_12, c_586, c_806])).
% 3.29/1.49  tff(c_812, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_22, c_18, c_14, c_10, c_811])).
% 3.29/1.49  tff(c_815, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_644, c_812])).
% 3.29/1.49  tff(c_818, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_815])).
% 3.29/1.49  tff(c_820, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_818])).
% 3.29/1.49  tff(c_821, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 3.29/1.49  tff(c_824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_587, c_821])).
% 3.29/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.49  
% 3.29/1.49  Inference rules
% 3.29/1.49  ----------------------
% 3.29/1.49  #Ref     : 0
% 3.29/1.49  #Sup     : 157
% 3.29/1.49  #Fact    : 0
% 3.29/1.49  #Define  : 0
% 3.29/1.49  #Split   : 12
% 3.29/1.49  #Chain   : 0
% 3.29/1.49  #Close   : 0
% 3.29/1.49  
% 3.29/1.49  Ordering : KBO
% 3.29/1.49  
% 3.29/1.49  Simplification rules
% 3.29/1.49  ----------------------
% 3.29/1.49  #Subsume      : 27
% 3.29/1.49  #Demod        : 115
% 3.29/1.49  #Tautology    : 40
% 3.29/1.49  #SimpNegUnit  : 105
% 3.29/1.49  #BackRed      : 0
% 3.29/1.49  
% 3.29/1.49  #Partial instantiations: 0
% 3.29/1.49  #Strategies tried      : 1
% 3.29/1.49  
% 3.29/1.49  Timing (in seconds)
% 3.29/1.49  ----------------------
% 3.29/1.49  Preprocessing        : 0.32
% 3.29/1.49  Parsing              : 0.17
% 3.29/1.49  CNF conversion       : 0.03
% 3.29/1.49  Main loop            : 0.40
% 3.29/1.49  Inferencing          : 0.15
% 3.29/1.49  Reduction            : 0.12
% 3.29/1.49  Demodulation         : 0.08
% 3.29/1.49  BG Simplification    : 0.02
% 3.29/1.49  Subsumption          : 0.08
% 3.29/1.49  Abstraction          : 0.03
% 3.29/1.49  MUC search           : 0.00
% 3.29/1.49  Cooper               : 0.00
% 3.29/1.49  Total                : 0.76
% 3.29/1.49  Index Insertion      : 0.00
% 3.29/1.49  Index Deletion       : 0.00
% 3.29/1.49  Index Matching       : 0.00
% 3.29/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
