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
% DateTime   : Thu Dec  3 10:19:17 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 201 expanded)
%              Number of leaves         :   18 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  147 ( 622 expanded)
%              Number of equality atoms :   26 (  96 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( m1_pre_topc(A,B)
            <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( l1_pre_topc(C)
             => ! [D] :
                  ( l1_pre_topc(D)
                 => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                      & g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D),u1_pre_topc(D))
                      & m1_pre_topc(C,A) )
                   => m1_pre_topc(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(c_14,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    ! [A_30] :
      ( m1_subset_1(u1_pre_topc(A_30),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_30))))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_pre_topc(g1_pre_topc(A_2,B_3))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    ! [A_30] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_30),u1_pre_topc(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_28,c_6])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( l1_pre_topc(g1_pre_topc(A_2,B_3))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_35,plain,(
    ! [A_30] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_30),u1_pre_topc(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_28,c_4])).

tff(c_24,plain,
    ( m1_pre_topc('#skF_1','#skF_2')
    | m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_54,plain,(
    m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_18,plain,
    ( ~ m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_67,plain,(
    ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_18])).

tff(c_16,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_68,plain,(
    ! [D_34,B_35,C_36,A_37] :
      ( m1_pre_topc(D_34,B_35)
      | ~ m1_pre_topc(C_36,A_37)
      | g1_pre_topc(u1_struct_0(D_34),u1_pre_topc(D_34)) != g1_pre_topc(u1_struct_0(C_36),u1_pre_topc(C_36))
      | g1_pre_topc(u1_struct_0(B_35),u1_pre_topc(B_35)) != g1_pre_topc(u1_struct_0(A_37),u1_pre_topc(A_37))
      | ~ l1_pre_topc(D_34)
      | ~ l1_pre_topc(C_36)
      | ~ l1_pre_topc(B_35)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_70,plain,(
    ! [D_34,B_35] :
      ( m1_pre_topc(D_34,B_35)
      | g1_pre_topc(u1_struct_0(D_34),u1_pre_topc(D_34)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) != g1_pre_topc(u1_struct_0(B_35),u1_pre_topc(B_35))
      | ~ l1_pre_topc(D_34)
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(B_35)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_54,c_68])).

tff(c_73,plain,(
    ! [D_34,B_35] :
      ( m1_pre_topc(D_34,B_35)
      | g1_pre_topc(u1_struct_0(D_34),u1_pre_topc(D_34)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) != g1_pre_topc(u1_struct_0(B_35),u1_pre_topc(B_35))
      | ~ l1_pre_topc(D_34)
      | ~ l1_pre_topc(B_35)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_70])).

tff(c_74,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_80,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_35,c_74])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_80])).

tff(c_88,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [D_34,B_35] :
      ( m1_pre_topc(D_34,B_35)
      | g1_pre_topc(u1_struct_0(D_34),u1_pre_topc(D_34)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) != g1_pre_topc(u1_struct_0(B_35),u1_pre_topc(B_35))
      | ~ l1_pre_topc(D_34)
      | ~ l1_pre_topc(B_35) ) ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_96,plain,(
    ! [B_35] :
      ( m1_pre_topc('#skF_1',B_35)
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) != g1_pre_topc(u1_struct_0(B_35),u1_pre_topc(B_35))
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(B_35) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_87])).

tff(c_122,plain,(
    ! [B_42] :
      ( m1_pre_topc('#skF_1',B_42)
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) != g1_pre_topc(u1_struct_0(B_42),u1_pre_topc(B_42))
      | ~ l1_pre_topc(B_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_96])).

tff(c_131,plain,(
    ! [B_42] :
      ( m1_pre_topc('#skF_1',B_42)
      | g1_pre_topc(u1_struct_0(B_42),u1_pre_topc(B_42)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc(B_42)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_122])).

tff(c_140,plain,(
    ! [B_42] :
      ( m1_pre_topc('#skF_1',B_42)
      | g1_pre_topc(u1_struct_0(B_42),u1_pre_topc(B_42)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc(B_42)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_131])).

tff(c_141,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_147,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_141])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_147])).

tff(c_154,plain,(
    ! [B_42] :
      ( m1_pre_topc('#skF_1',B_42)
      | g1_pre_topc(u1_struct_0(B_42),u1_pre_topc(B_42)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc(B_42) ) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_164,plain,
    ( m1_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_154])).

tff(c_166,plain,(
    m1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_164])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_166])).

tff(c_170,plain,(
    ~ m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_169,plain,(
    m1_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_184,plain,(
    ! [D_43,B_44,C_45,A_46] :
      ( m1_pre_topc(D_43,B_44)
      | ~ m1_pre_topc(C_45,A_46)
      | g1_pre_topc(u1_struct_0(D_43),u1_pre_topc(D_43)) != g1_pre_topc(u1_struct_0(C_45),u1_pre_topc(C_45))
      | g1_pre_topc(u1_struct_0(B_44),u1_pre_topc(B_44)) != g1_pre_topc(u1_struct_0(A_46),u1_pre_topc(A_46))
      | ~ l1_pre_topc(D_43)
      | ~ l1_pre_topc(C_45)
      | ~ l1_pre_topc(B_44)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_186,plain,(
    ! [D_43,B_44] :
      ( m1_pre_topc(D_43,B_44)
      | g1_pre_topc(u1_struct_0(D_43),u1_pre_topc(D_43)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | g1_pre_topc(u1_struct_0(B_44),u1_pre_topc(B_44)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc(D_43)
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(B_44)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_169,c_184])).

tff(c_189,plain,(
    ! [D_43,B_44] :
      ( m1_pre_topc(D_43,B_44)
      | g1_pre_topc(u1_struct_0(D_43),u1_pre_topc(D_43)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | g1_pre_topc(u1_struct_0(B_44),u1_pre_topc(B_44)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc(D_43)
      | ~ l1_pre_topc(B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_186])).

tff(c_192,plain,(
    ! [B_44] :
      ( m1_pre_topc('#skF_1',B_44)
      | g1_pre_topc(u1_struct_0(B_44),u1_pre_topc(B_44)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(B_44) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_189])).

tff(c_208,plain,(
    ! [B_49] :
      ( m1_pre_topc('#skF_1',B_49)
      | g1_pre_topc(u1_struct_0(B_49),u1_pre_topc(B_49)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc(B_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_192])).

tff(c_211,plain,(
    ! [A_1] :
      ( m1_pre_topc('#skF_1',A_1)
      | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != A_1
      | ~ l1_pre_topc(A_1)
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_208])).

tff(c_220,plain,
    ( m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_211])).

tff(c_221,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_220])).

tff(c_228,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_234,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_35,c_228])).

tff(c_240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_234])).

tff(c_242,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_241,plain,
    ( ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_250,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_241])).

tff(c_256,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_250])).

tff(c_262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_256])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.42  
% 2.29/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.42  %$ m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.29/1.42  
% 2.29/1.42  %Foreground sorts:
% 2.29/1.42  
% 2.29/1.42  
% 2.29/1.42  %Background operators:
% 2.29/1.42  
% 2.29/1.42  
% 2.29/1.42  %Foreground operators:
% 2.29/1.42  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.29/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.42  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.29/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.29/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.42  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.29/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.42  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.29/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.29/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.42  
% 2.29/1.44  tff(f_77, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 2.29/1.44  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.29/1.44  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 2.29/1.44  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (l1_pre_topc(C) => (![D]: (l1_pre_topc(D) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D), u1_pre_topc(D)))) & m1_pre_topc(C, A)) => m1_pre_topc(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_pre_topc)).
% 2.29/1.44  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 2.29/1.44  tff(c_14, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.29/1.44  tff(c_28, plain, (![A_30]: (m1_subset_1(u1_pre_topc(A_30), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_30)))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.29/1.44  tff(c_6, plain, (![A_2, B_3]: (v1_pre_topc(g1_pre_topc(A_2, B_3)) | ~m1_subset_1(B_3, k1_zfmisc_1(k1_zfmisc_1(A_2))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.29/1.44  tff(c_36, plain, (![A_30]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_30), u1_pre_topc(A_30))) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_28, c_6])).
% 2.29/1.44  tff(c_4, plain, (![A_2, B_3]: (l1_pre_topc(g1_pre_topc(A_2, B_3)) | ~m1_subset_1(B_3, k1_zfmisc_1(k1_zfmisc_1(A_2))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.29/1.44  tff(c_35, plain, (![A_30]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_30), u1_pre_topc(A_30))) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_28, c_4])).
% 2.29/1.44  tff(c_24, plain, (m1_pre_topc('#skF_1', '#skF_2') | m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.29/1.44  tff(c_54, plain, (m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_24])).
% 2.29/1.44  tff(c_18, plain, (~m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.29/1.44  tff(c_67, plain, (~m1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_18])).
% 2.29/1.44  tff(c_16, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.29/1.44  tff(c_68, plain, (![D_34, B_35, C_36, A_37]: (m1_pre_topc(D_34, B_35) | ~m1_pre_topc(C_36, A_37) | g1_pre_topc(u1_struct_0(D_34), u1_pre_topc(D_34))!=g1_pre_topc(u1_struct_0(C_36), u1_pre_topc(C_36)) | g1_pre_topc(u1_struct_0(B_35), u1_pre_topc(B_35))!=g1_pre_topc(u1_struct_0(A_37), u1_pre_topc(A_37)) | ~l1_pre_topc(D_34) | ~l1_pre_topc(C_36) | ~l1_pre_topc(B_35) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.29/1.44  tff(c_70, plain, (![D_34, B_35]: (m1_pre_topc(D_34, B_35) | g1_pre_topc(u1_struct_0(D_34), u1_pre_topc(D_34))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))!=g1_pre_topc(u1_struct_0(B_35), u1_pre_topc(B_35)) | ~l1_pre_topc(D_34) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(B_35) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_54, c_68])).
% 2.29/1.44  tff(c_73, plain, (![D_34, B_35]: (m1_pre_topc(D_34, B_35) | g1_pre_topc(u1_struct_0(D_34), u1_pre_topc(D_34))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))!=g1_pre_topc(u1_struct_0(B_35), u1_pre_topc(B_35)) | ~l1_pre_topc(D_34) | ~l1_pre_topc(B_35) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_70])).
% 2.29/1.44  tff(c_74, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_73])).
% 2.29/1.44  tff(c_80, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_35, c_74])).
% 2.29/1.44  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_80])).
% 2.29/1.44  tff(c_88, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_73])).
% 2.29/1.44  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.44  tff(c_87, plain, (![D_34, B_35]: (m1_pre_topc(D_34, B_35) | g1_pre_topc(u1_struct_0(D_34), u1_pre_topc(D_34))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))!=g1_pre_topc(u1_struct_0(B_35), u1_pre_topc(B_35)) | ~l1_pre_topc(D_34) | ~l1_pre_topc(B_35))), inference(splitRight, [status(thm)], [c_73])).
% 2.29/1.44  tff(c_96, plain, (![B_35]: (m1_pre_topc('#skF_1', B_35) | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))!=g1_pre_topc(u1_struct_0(B_35), u1_pre_topc(B_35)) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(B_35))), inference(reflexivity, [status(thm), theory('equality')], [c_87])).
% 2.29/1.44  tff(c_122, plain, (![B_42]: (m1_pre_topc('#skF_1', B_42) | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))!=g1_pre_topc(u1_struct_0(B_42), u1_pre_topc(B_42)) | ~l1_pre_topc(B_42))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_96])).
% 2.29/1.44  tff(c_131, plain, (![B_42]: (m1_pre_topc('#skF_1', B_42) | g1_pre_topc(u1_struct_0(B_42), u1_pre_topc(B_42))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc(B_42) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_122])).
% 2.29/1.44  tff(c_140, plain, (![B_42]: (m1_pre_topc('#skF_1', B_42) | g1_pre_topc(u1_struct_0(B_42), u1_pre_topc(B_42))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc(B_42) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_131])).
% 2.29/1.44  tff(c_141, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_140])).
% 2.29/1.44  tff(c_147, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_141])).
% 2.29/1.44  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_147])).
% 2.29/1.44  tff(c_154, plain, (![B_42]: (m1_pre_topc('#skF_1', B_42) | g1_pre_topc(u1_struct_0(B_42), u1_pre_topc(B_42))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc(B_42))), inference(splitRight, [status(thm)], [c_140])).
% 2.29/1.44  tff(c_164, plain, (m1_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_154])).
% 2.29/1.44  tff(c_166, plain, (m1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_164])).
% 2.29/1.44  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_166])).
% 2.29/1.44  tff(c_170, plain, (~m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_24])).
% 2.29/1.44  tff(c_169, plain, (m1_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_24])).
% 2.29/1.44  tff(c_184, plain, (![D_43, B_44, C_45, A_46]: (m1_pre_topc(D_43, B_44) | ~m1_pre_topc(C_45, A_46) | g1_pre_topc(u1_struct_0(D_43), u1_pre_topc(D_43))!=g1_pre_topc(u1_struct_0(C_45), u1_pre_topc(C_45)) | g1_pre_topc(u1_struct_0(B_44), u1_pre_topc(B_44))!=g1_pre_topc(u1_struct_0(A_46), u1_pre_topc(A_46)) | ~l1_pre_topc(D_43) | ~l1_pre_topc(C_45) | ~l1_pre_topc(B_44) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.29/1.44  tff(c_186, plain, (![D_43, B_44]: (m1_pre_topc(D_43, B_44) | g1_pre_topc(u1_struct_0(D_43), u1_pre_topc(D_43))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | g1_pre_topc(u1_struct_0(B_44), u1_pre_topc(B_44))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc(D_43) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(B_44) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_169, c_184])).
% 2.29/1.44  tff(c_189, plain, (![D_43, B_44]: (m1_pre_topc(D_43, B_44) | g1_pre_topc(u1_struct_0(D_43), u1_pre_topc(D_43))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | g1_pre_topc(u1_struct_0(B_44), u1_pre_topc(B_44))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc(D_43) | ~l1_pre_topc(B_44))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_186])).
% 2.29/1.44  tff(c_192, plain, (![B_44]: (m1_pre_topc('#skF_1', B_44) | g1_pre_topc(u1_struct_0(B_44), u1_pre_topc(B_44))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(B_44))), inference(reflexivity, [status(thm), theory('equality')], [c_189])).
% 2.29/1.44  tff(c_208, plain, (![B_49]: (m1_pre_topc('#skF_1', B_49) | g1_pre_topc(u1_struct_0(B_49), u1_pre_topc(B_49))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc(B_49))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_192])).
% 2.29/1.44  tff(c_211, plain, (![A_1]: (m1_pre_topc('#skF_1', A_1) | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=A_1 | ~l1_pre_topc(A_1) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_208])).
% 2.29/1.44  tff(c_220, plain, (m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(reflexivity, [status(thm), theory('equality')], [c_211])).
% 2.29/1.44  tff(c_221, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_170, c_220])).
% 2.29/1.44  tff(c_228, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_221])).
% 2.29/1.44  tff(c_234, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_35, c_228])).
% 2.29/1.44  tff(c_240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_234])).
% 2.29/1.44  tff(c_242, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_221])).
% 2.29/1.44  tff(c_241, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_221])).
% 2.29/1.44  tff(c_250, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_241])).
% 2.29/1.44  tff(c_256, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_250])).
% 2.29/1.44  tff(c_262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_256])).
% 2.29/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.44  
% 2.29/1.44  Inference rules
% 2.29/1.44  ----------------------
% 2.29/1.44  #Ref     : 7
% 2.29/1.44  #Sup     : 35
% 2.29/1.44  #Fact    : 0
% 2.29/1.44  #Define  : 0
% 2.29/1.44  #Split   : 6
% 2.29/1.44  #Chain   : 0
% 2.29/1.44  #Close   : 0
% 2.29/1.44  
% 2.29/1.44  Ordering : KBO
% 2.29/1.44  
% 2.29/1.44  Simplification rules
% 2.29/1.44  ----------------------
% 2.29/1.44  #Subsume      : 12
% 2.29/1.44  #Demod        : 42
% 2.29/1.44  #Tautology    : 10
% 2.29/1.44  #SimpNegUnit  : 3
% 2.29/1.44  #BackRed      : 0
% 2.29/1.44  
% 2.29/1.44  #Partial instantiations: 0
% 2.29/1.44  #Strategies tried      : 1
% 2.29/1.44  
% 2.29/1.44  Timing (in seconds)
% 2.29/1.44  ----------------------
% 2.29/1.44  Preprocessing        : 0.40
% 2.29/1.44  Parsing              : 0.21
% 2.29/1.44  CNF conversion       : 0.03
% 2.29/1.44  Main loop            : 0.24
% 2.29/1.44  Inferencing          : 0.09
% 2.29/1.44  Reduction            : 0.07
% 2.29/1.44  Demodulation         : 0.05
% 2.29/1.44  BG Simplification    : 0.02
% 2.29/1.44  Subsumption          : 0.05
% 2.29/1.45  Abstraction          : 0.01
% 2.29/1.45  MUC search           : 0.00
% 2.29/1.45  Cooper               : 0.00
% 2.29/1.45  Total                : 0.68
% 2.29/1.45  Index Insertion      : 0.00
% 2.29/1.45  Index Deletion       : 0.00
% 2.29/1.45  Index Matching       : 0.00
% 2.29/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
