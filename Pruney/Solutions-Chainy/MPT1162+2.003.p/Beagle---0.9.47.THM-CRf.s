%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:47 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 338 expanded)
%              Number of leaves         :   26 ( 141 expanded)
%              Depth                    :   19
%              Number of atoms          :  311 (1700 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
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
                   => ( r2_orders_2(A,B,C)
                     => r1_tarski(k3_orders_2(A,D,B),k3_orders_2(A,D,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_102,axiom,(
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

tff(f_76,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_orders_2)).

tff(c_20,plain,(
    ~ r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_36,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_30,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,(
    ! [A_64,B_65,C_66] :
      ( m1_subset_1(k3_orders_2(A_64,B_65,C_66),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1(C_66,u1_struct_0(A_64))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_orders_2(A_64)
      | ~ v5_orders_2(A_64)
      | ~ v4_orders_2(A_64)
      | ~ v3_orders_2(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( m1_subset_1(A_6,C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_95,plain,(
    ! [A_81,A_82,B_83,C_84] :
      ( m1_subset_1(A_81,u1_struct_0(A_82))
      | ~ r2_hidden(A_81,k3_orders_2(A_82,B_83,C_84))
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_55,c_8])).

tff(c_103,plain,(
    ! [A_82,B_83,C_84,B_2] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_82,B_83,C_84),B_2),u1_struct_0(A_82))
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82)
      | r1_tarski(k3_orders_2(A_82,B_83,C_84),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_104,plain,(
    ! [B_85,D_86,A_87,C_88] :
      ( r2_hidden(B_85,D_86)
      | ~ r2_hidden(B_85,k3_orders_2(A_87,D_86,C_88))
      | ~ m1_subset_1(D_86,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_subset_1(C_88,u1_struct_0(A_87))
      | ~ m1_subset_1(B_85,u1_struct_0(A_87))
      | ~ l1_orders_2(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v4_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_194,plain,(
    ! [A_119,D_120,C_121,B_122] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_119,D_120,C_121),B_122),D_120)
      | ~ m1_subset_1(D_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_subset_1(C_121,u1_struct_0(A_119))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_119,D_120,C_121),B_122),u1_struct_0(A_119))
      | ~ l1_orders_2(A_119)
      | ~ v5_orders_2(A_119)
      | ~ v4_orders_2(A_119)
      | ~ v3_orders_2(A_119)
      | v2_struct_0(A_119)
      | r1_tarski(k3_orders_2(A_119,D_120,C_121),B_122) ) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_206,plain,(
    ! [A_82,B_83,C_84,B_2] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_82,B_83,C_84),B_2),B_83)
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82)
      | r1_tarski(k3_orders_2(A_82,B_83,C_84),B_2) ) ),
    inference(resolution,[status(thm)],[c_103,c_194])).

tff(c_40,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [A_55] : r1_tarski(A_55,A_55) ),
    inference(resolution,[status(thm)],[c_40,c_4])).

tff(c_47,plain,(
    ! [C_58,B_59,A_60] :
      ( r2_hidden(C_58,B_59)
      | ~ r2_hidden(C_58,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [A_1,B_2,B_59] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_59)
      | ~ r1_tarski(A_1,B_59)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_174,plain,(
    ! [B_111,A_113,A_112,B_110,C_109] :
      ( m1_subset_1('#skF_1'(A_112,B_111),u1_struct_0(A_113))
      | ~ m1_subset_1(C_109,u1_struct_0(A_113))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_orders_2(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v4_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113)
      | ~ r1_tarski(A_112,k3_orders_2(A_113,B_110,C_109))
      | r1_tarski(A_112,B_111) ) ),
    inference(resolution,[status(thm)],[c_50,c_95])).

tff(c_178,plain,(
    ! [A_112,B_111,C_109] :
      ( m1_subset_1('#skF_1'(A_112,B_111),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_109,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_112,k3_orders_2('#skF_2','#skF_5',C_109))
      | r1_tarski(A_112,B_111) ) ),
    inference(resolution,[status(thm)],[c_24,c_174])).

tff(c_182,plain,(
    ! [A_112,B_111,C_109] :
      ( m1_subset_1('#skF_1'(A_112,B_111),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_109,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_112,k3_orders_2('#skF_2','#skF_5',C_109))
      | r1_tarski(A_112,B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_178])).

tff(c_184,plain,(
    ! [A_114,B_115,C_116] :
      ( m1_subset_1('#skF_1'(A_114,B_115),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_116,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_114,k3_orders_2('#skF_2','#skF_5',C_116))
      | r1_tarski(A_114,B_115) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_182])).

tff(c_188,plain,(
    ! [C_116,B_115] :
      ( m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_116),B_115),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_116,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_116),B_115) ) ),
    inference(resolution,[status(thm)],[c_45,c_184])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_113,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( r2_orders_2(A_89,B_90,C_91)
      | ~ r2_hidden(B_90,k3_orders_2(A_89,D_92,C_91))
      | ~ m1_subset_1(D_92,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ m1_subset_1(C_91,u1_struct_0(A_89))
      | ~ m1_subset_1(B_90,u1_struct_0(A_89))
      | ~ l1_orders_2(A_89)
      | ~ v5_orders_2(A_89)
      | ~ v4_orders_2(A_89)
      | ~ v3_orders_2(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_309,plain,(
    ! [A_145,D_146,C_147,B_148] :
      ( r2_orders_2(A_145,'#skF_1'(k3_orders_2(A_145,D_146,C_147),B_148),C_147)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ m1_subset_1(C_147,u1_struct_0(A_145))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_145,D_146,C_147),B_148),u1_struct_0(A_145))
      | ~ l1_orders_2(A_145)
      | ~ v5_orders_2(A_145)
      | ~ v4_orders_2(A_145)
      | ~ v3_orders_2(A_145)
      | v2_struct_0(A_145)
      | r1_tarski(k3_orders_2(A_145,D_146,C_147),B_148) ) ),
    inference(resolution,[status(thm)],[c_6,c_113])).

tff(c_311,plain,(
    ! [C_116,B_115] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_116),B_115),C_116)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_116,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_116),B_115) ) ),
    inference(resolution,[status(thm)],[c_188,c_309])).

tff(c_319,plain,(
    ! [C_116,B_115] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_116),B_115),C_116)
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_116,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_116),B_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_24,c_311])).

tff(c_326,plain,(
    ! [C_149,B_150] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_149),B_150),C_149)
      | ~ m1_subset_1(C_149,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_149),B_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_319])).

tff(c_122,plain,(
    ! [A_93,B_94,C_95,B_96] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_93,B_94,C_95),B_96),u1_struct_0(A_93))
      | ~ m1_subset_1(C_95,u1_struct_0(A_93))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_orders_2(A_93)
      | ~ v5_orders_2(A_93)
      | ~ v4_orders_2(A_93)
      | ~ v3_orders_2(A_93)
      | v2_struct_0(A_93)
      | r1_tarski(k3_orders_2(A_93,B_94,C_95),B_96) ) ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_22,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_73,plain,(
    ! [A_75,B_76,D_77,C_78] :
      ( r2_orders_2(A_75,B_76,D_77)
      | ~ r2_orders_2(A_75,C_78,D_77)
      | ~ r2_orders_2(A_75,B_76,C_78)
      | ~ m1_subset_1(D_77,u1_struct_0(A_75))
      | ~ m1_subset_1(C_78,u1_struct_0(A_75))
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_orders_2(A_75)
      | ~ v5_orders_2(A_75)
      | ~ v4_orders_2(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_75,plain,(
    ! [B_76] :
      ( r2_orders_2('#skF_2',B_76,'#skF_4')
      | ~ r2_orders_2('#skF_2',B_76,'#skF_3')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_76,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_78,plain,(
    ! [B_76] :
      ( r2_orders_2('#skF_2',B_76,'#skF_4')
      | ~ r2_orders_2('#skF_2',B_76,'#skF_3')
      | ~ m1_subset_1(B_76,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_75])).

tff(c_126,plain,(
    ! [B_94,C_95,B_96] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',B_94,C_95),B_96),'#skF_4')
      | ~ r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',B_94,C_95),B_96),'#skF_3')
      | ~ m1_subset_1(C_95,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2',B_94,C_95),B_96) ) ),
    inference(resolution,[status(thm)],[c_122,c_78])).

tff(c_129,plain,(
    ! [B_94,C_95,B_96] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',B_94,C_95),B_96),'#skF_4')
      | ~ r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',B_94,C_95),B_96),'#skF_3')
      | ~ m1_subset_1(C_95,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2',B_94,C_95),B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_126])).

tff(c_130,plain,(
    ! [B_94,C_95,B_96] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',B_94,C_95),B_96),'#skF_4')
      | ~ r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',B_94,C_95),B_96),'#skF_3')
      | ~ m1_subset_1(C_95,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski(k3_orders_2('#skF_2',B_94,C_95),B_96) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_129])).

tff(c_330,plain,(
    ! [B_150] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),B_150),'#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),B_150) ) ),
    inference(resolution,[status(thm)],[c_326,c_130])).

tff(c_339,plain,(
    ! [B_150] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),B_150),'#skF_4')
      | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),B_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_330])).

tff(c_132,plain,(
    ! [B_100,A_101,D_102,C_103] :
      ( r2_hidden(B_100,k3_orders_2(A_101,D_102,C_103))
      | ~ r2_hidden(B_100,D_102)
      | ~ r2_orders_2(A_101,B_100,C_103)
      | ~ m1_subset_1(D_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m1_subset_1(C_103,u1_struct_0(A_101))
      | ~ m1_subset_1(B_100,u1_struct_0(A_101))
      | ~ l1_orders_2(A_101)
      | ~ v5_orders_2(A_101)
      | ~ v4_orders_2(A_101)
      | ~ v3_orders_2(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_136,plain,(
    ! [B_100,C_103] :
      ( r2_hidden(B_100,k3_orders_2('#skF_2','#skF_5',C_103))
      | ~ r2_hidden(B_100,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_100,C_103)
      | ~ m1_subset_1(C_103,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_132])).

tff(c_140,plain,(
    ! [B_100,C_103] :
      ( r2_hidden(B_100,k3_orders_2('#skF_2','#skF_5',C_103))
      | ~ r2_hidden(B_100,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_100,C_103)
      | ~ m1_subset_1(C_103,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_136])).

tff(c_142,plain,(
    ! [B_104,C_105] :
      ( r2_hidden(B_104,k3_orders_2('#skF_2','#skF_5',C_105))
      | ~ r2_hidden(B_104,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_104,C_105)
      | ~ m1_subset_1(C_105,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_140])).

tff(c_611,plain,(
    ! [A_199,C_200] :
      ( r1_tarski(A_199,k3_orders_2('#skF_2','#skF_5',C_200))
      | ~ r2_hidden('#skF_1'(A_199,k3_orders_2('#skF_2','#skF_5',C_200)),'#skF_5')
      | ~ r2_orders_2('#skF_2','#skF_1'(A_199,k3_orders_2('#skF_2','#skF_5',C_200)),C_200)
      | ~ m1_subset_1(C_200,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_199,k3_orders_2('#skF_2','#skF_5',C_200)),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_142,c_4])).

tff(c_623,plain,
    ( ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_2'))
    | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_339,c_611])).

tff(c_637,plain,
    ( ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
    | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_2'))
    | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_623])).

tff(c_638,plain,
    ( ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
    | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_637])).

tff(c_641,plain,(
    ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_638])).

tff(c_644,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_188,c_641])).

tff(c_653,plain,(
    r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_644])).

tff(c_655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_653])).

tff(c_656,plain,(
    ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_638])).

tff(c_660,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_206,c_656])).

tff(c_678,plain,
    ( v2_struct_0('#skF_2')
    | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_24,c_28,c_660])).

tff(c_680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_38,c_678])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.48  
% 3.33/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.48  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.33/1.48  
% 3.33/1.48  %Foreground sorts:
% 3.33/1.48  
% 3.33/1.48  
% 3.33/1.48  %Background operators:
% 3.33/1.48  
% 3.33/1.48  
% 3.33/1.48  %Foreground operators:
% 3.33/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.33/1.48  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.33/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.48  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.33/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.48  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.33/1.48  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.33/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.48  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.33/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.48  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.33/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.33/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.48  
% 3.33/1.50  tff(f_127, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_orders_2(A, B, C) => r1_tarski(k3_orders_2(A, D, B), k3_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_orders_2)).
% 3.33/1.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.33/1.50  tff(f_55, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 3.33/1.50  tff(f_38, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.33/1.50  tff(f_102, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 3.33/1.50  tff(f_76, axiom, (![A]: (((v4_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_orders_2(A, B, C) & r2_orders_2(A, C, D)) => r2_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_orders_2)).
% 3.33/1.50  tff(c_20, plain, (~r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.33/1.50  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.33/1.50  tff(c_36, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.33/1.50  tff(c_34, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.33/1.50  tff(c_32, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.33/1.50  tff(c_30, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.33/1.50  tff(c_24, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.33/1.50  tff(c_28, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.33/1.50  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.33/1.50  tff(c_55, plain, (![A_64, B_65, C_66]: (m1_subset_1(k3_orders_2(A_64, B_65, C_66), k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1(C_66, u1_struct_0(A_64)) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_orders_2(A_64) | ~v5_orders_2(A_64) | ~v4_orders_2(A_64) | ~v3_orders_2(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.33/1.50  tff(c_8, plain, (![A_6, C_8, B_7]: (m1_subset_1(A_6, C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.33/1.50  tff(c_95, plain, (![A_81, A_82, B_83, C_84]: (m1_subset_1(A_81, u1_struct_0(A_82)) | ~r2_hidden(A_81, k3_orders_2(A_82, B_83, C_84)) | ~m1_subset_1(C_84, u1_struct_0(A_82)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82))), inference(resolution, [status(thm)], [c_55, c_8])).
% 3.33/1.50  tff(c_103, plain, (![A_82, B_83, C_84, B_2]: (m1_subset_1('#skF_1'(k3_orders_2(A_82, B_83, C_84), B_2), u1_struct_0(A_82)) | ~m1_subset_1(C_84, u1_struct_0(A_82)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82) | r1_tarski(k3_orders_2(A_82, B_83, C_84), B_2))), inference(resolution, [status(thm)], [c_6, c_95])).
% 3.33/1.50  tff(c_104, plain, (![B_85, D_86, A_87, C_88]: (r2_hidden(B_85, D_86) | ~r2_hidden(B_85, k3_orders_2(A_87, D_86, C_88)) | ~m1_subset_1(D_86, k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_subset_1(C_88, u1_struct_0(A_87)) | ~m1_subset_1(B_85, u1_struct_0(A_87)) | ~l1_orders_2(A_87) | ~v5_orders_2(A_87) | ~v4_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.33/1.50  tff(c_194, plain, (![A_119, D_120, C_121, B_122]: (r2_hidden('#skF_1'(k3_orders_2(A_119, D_120, C_121), B_122), D_120) | ~m1_subset_1(D_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_subset_1(C_121, u1_struct_0(A_119)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_119, D_120, C_121), B_122), u1_struct_0(A_119)) | ~l1_orders_2(A_119) | ~v5_orders_2(A_119) | ~v4_orders_2(A_119) | ~v3_orders_2(A_119) | v2_struct_0(A_119) | r1_tarski(k3_orders_2(A_119, D_120, C_121), B_122))), inference(resolution, [status(thm)], [c_6, c_104])).
% 3.33/1.50  tff(c_206, plain, (![A_82, B_83, C_84, B_2]: (r2_hidden('#skF_1'(k3_orders_2(A_82, B_83, C_84), B_2), B_83) | ~m1_subset_1(C_84, u1_struct_0(A_82)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82) | r1_tarski(k3_orders_2(A_82, B_83, C_84), B_2))), inference(resolution, [status(thm)], [c_103, c_194])).
% 3.33/1.50  tff(c_40, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.33/1.50  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.33/1.50  tff(c_45, plain, (![A_55]: (r1_tarski(A_55, A_55))), inference(resolution, [status(thm)], [c_40, c_4])).
% 3.33/1.50  tff(c_47, plain, (![C_58, B_59, A_60]: (r2_hidden(C_58, B_59) | ~r2_hidden(C_58, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.33/1.50  tff(c_50, plain, (![A_1, B_2, B_59]: (r2_hidden('#skF_1'(A_1, B_2), B_59) | ~r1_tarski(A_1, B_59) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_47])).
% 3.33/1.50  tff(c_174, plain, (![B_111, A_113, A_112, B_110, C_109]: (m1_subset_1('#skF_1'(A_112, B_111), u1_struct_0(A_113)) | ~m1_subset_1(C_109, u1_struct_0(A_113)) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_orders_2(A_113) | ~v5_orders_2(A_113) | ~v4_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113) | ~r1_tarski(A_112, k3_orders_2(A_113, B_110, C_109)) | r1_tarski(A_112, B_111))), inference(resolution, [status(thm)], [c_50, c_95])).
% 3.33/1.50  tff(c_178, plain, (![A_112, B_111, C_109]: (m1_subset_1('#skF_1'(A_112, B_111), u1_struct_0('#skF_2')) | ~m1_subset_1(C_109, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_112, k3_orders_2('#skF_2', '#skF_5', C_109)) | r1_tarski(A_112, B_111))), inference(resolution, [status(thm)], [c_24, c_174])).
% 3.33/1.50  tff(c_182, plain, (![A_112, B_111, C_109]: (m1_subset_1('#skF_1'(A_112, B_111), u1_struct_0('#skF_2')) | ~m1_subset_1(C_109, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(A_112, k3_orders_2('#skF_2', '#skF_5', C_109)) | r1_tarski(A_112, B_111))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_178])).
% 3.33/1.50  tff(c_184, plain, (![A_114, B_115, C_116]: (m1_subset_1('#skF_1'(A_114, B_115), u1_struct_0('#skF_2')) | ~m1_subset_1(C_116, u1_struct_0('#skF_2')) | ~r1_tarski(A_114, k3_orders_2('#skF_2', '#skF_5', C_116)) | r1_tarski(A_114, B_115))), inference(negUnitSimplification, [status(thm)], [c_38, c_182])).
% 3.33/1.50  tff(c_188, plain, (![C_116, B_115]: (m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_116), B_115), u1_struct_0('#skF_2')) | ~m1_subset_1(C_116, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_116), B_115))), inference(resolution, [status(thm)], [c_45, c_184])).
% 3.33/1.50  tff(c_26, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.33/1.50  tff(c_113, plain, (![A_89, B_90, C_91, D_92]: (r2_orders_2(A_89, B_90, C_91) | ~r2_hidden(B_90, k3_orders_2(A_89, D_92, C_91)) | ~m1_subset_1(D_92, k1_zfmisc_1(u1_struct_0(A_89))) | ~m1_subset_1(C_91, u1_struct_0(A_89)) | ~m1_subset_1(B_90, u1_struct_0(A_89)) | ~l1_orders_2(A_89) | ~v5_orders_2(A_89) | ~v4_orders_2(A_89) | ~v3_orders_2(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.33/1.50  tff(c_309, plain, (![A_145, D_146, C_147, B_148]: (r2_orders_2(A_145, '#skF_1'(k3_orders_2(A_145, D_146, C_147), B_148), C_147) | ~m1_subset_1(D_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~m1_subset_1(C_147, u1_struct_0(A_145)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_145, D_146, C_147), B_148), u1_struct_0(A_145)) | ~l1_orders_2(A_145) | ~v5_orders_2(A_145) | ~v4_orders_2(A_145) | ~v3_orders_2(A_145) | v2_struct_0(A_145) | r1_tarski(k3_orders_2(A_145, D_146, C_147), B_148))), inference(resolution, [status(thm)], [c_6, c_113])).
% 3.33/1.50  tff(c_311, plain, (![C_116, B_115]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_116), B_115), C_116) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_116, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_116), B_115))), inference(resolution, [status(thm)], [c_188, c_309])).
% 3.33/1.50  tff(c_319, plain, (![C_116, B_115]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_116), B_115), C_116) | v2_struct_0('#skF_2') | ~m1_subset_1(C_116, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_116), B_115))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_24, c_311])).
% 3.33/1.50  tff(c_326, plain, (![C_149, B_150]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_149), B_150), C_149) | ~m1_subset_1(C_149, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_149), B_150))), inference(negUnitSimplification, [status(thm)], [c_38, c_319])).
% 3.33/1.50  tff(c_122, plain, (![A_93, B_94, C_95, B_96]: (m1_subset_1('#skF_1'(k3_orders_2(A_93, B_94, C_95), B_96), u1_struct_0(A_93)) | ~m1_subset_1(C_95, u1_struct_0(A_93)) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_orders_2(A_93) | ~v5_orders_2(A_93) | ~v4_orders_2(A_93) | ~v3_orders_2(A_93) | v2_struct_0(A_93) | r1_tarski(k3_orders_2(A_93, B_94, C_95), B_96))), inference(resolution, [status(thm)], [c_6, c_95])).
% 3.33/1.50  tff(c_22, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.33/1.50  tff(c_73, plain, (![A_75, B_76, D_77, C_78]: (r2_orders_2(A_75, B_76, D_77) | ~r2_orders_2(A_75, C_78, D_77) | ~r2_orders_2(A_75, B_76, C_78) | ~m1_subset_1(D_77, u1_struct_0(A_75)) | ~m1_subset_1(C_78, u1_struct_0(A_75)) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l1_orders_2(A_75) | ~v5_orders_2(A_75) | ~v4_orders_2(A_75))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.33/1.50  tff(c_75, plain, (![B_76]: (r2_orders_2('#skF_2', B_76, '#skF_4') | ~r2_orders_2('#skF_2', B_76, '#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_76, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_73])).
% 3.33/1.50  tff(c_78, plain, (![B_76]: (r2_orders_2('#skF_2', B_76, '#skF_4') | ~r2_orders_2('#skF_2', B_76, '#skF_3') | ~m1_subset_1(B_76, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_26, c_75])).
% 3.33/1.50  tff(c_126, plain, (![B_94, C_95, B_96]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', B_94, C_95), B_96), '#skF_4') | ~r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', B_94, C_95), B_96), '#skF_3') | ~m1_subset_1(C_95, u1_struct_0('#skF_2')) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', B_94, C_95), B_96))), inference(resolution, [status(thm)], [c_122, c_78])).
% 3.33/1.50  tff(c_129, plain, (![B_94, C_95, B_96]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', B_94, C_95), B_96), '#skF_4') | ~r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', B_94, C_95), B_96), '#skF_3') | ~m1_subset_1(C_95, u1_struct_0('#skF_2')) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', B_94, C_95), B_96))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_126])).
% 3.33/1.50  tff(c_130, plain, (![B_94, C_95, B_96]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', B_94, C_95), B_96), '#skF_4') | ~r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', B_94, C_95), B_96), '#skF_3') | ~m1_subset_1(C_95, u1_struct_0('#skF_2')) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski(k3_orders_2('#skF_2', B_94, C_95), B_96))), inference(negUnitSimplification, [status(thm)], [c_38, c_129])).
% 3.33/1.50  tff(c_330, plain, (![B_150]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), B_150), '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), B_150))), inference(resolution, [status(thm)], [c_326, c_130])).
% 3.33/1.50  tff(c_339, plain, (![B_150]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), B_150), '#skF_4') | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), B_150))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_330])).
% 3.33/1.50  tff(c_132, plain, (![B_100, A_101, D_102, C_103]: (r2_hidden(B_100, k3_orders_2(A_101, D_102, C_103)) | ~r2_hidden(B_100, D_102) | ~r2_orders_2(A_101, B_100, C_103) | ~m1_subset_1(D_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~m1_subset_1(C_103, u1_struct_0(A_101)) | ~m1_subset_1(B_100, u1_struct_0(A_101)) | ~l1_orders_2(A_101) | ~v5_orders_2(A_101) | ~v4_orders_2(A_101) | ~v3_orders_2(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.33/1.50  tff(c_136, plain, (![B_100, C_103]: (r2_hidden(B_100, k3_orders_2('#skF_2', '#skF_5', C_103)) | ~r2_hidden(B_100, '#skF_5') | ~r2_orders_2('#skF_2', B_100, C_103) | ~m1_subset_1(C_103, u1_struct_0('#skF_2')) | ~m1_subset_1(B_100, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_132])).
% 3.33/1.50  tff(c_140, plain, (![B_100, C_103]: (r2_hidden(B_100, k3_orders_2('#skF_2', '#skF_5', C_103)) | ~r2_hidden(B_100, '#skF_5') | ~r2_orders_2('#skF_2', B_100, C_103) | ~m1_subset_1(C_103, u1_struct_0('#skF_2')) | ~m1_subset_1(B_100, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_136])).
% 3.33/1.50  tff(c_142, plain, (![B_104, C_105]: (r2_hidden(B_104, k3_orders_2('#skF_2', '#skF_5', C_105)) | ~r2_hidden(B_104, '#skF_5') | ~r2_orders_2('#skF_2', B_104, C_105) | ~m1_subset_1(C_105, u1_struct_0('#skF_2')) | ~m1_subset_1(B_104, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_38, c_140])).
% 3.33/1.50  tff(c_611, plain, (![A_199, C_200]: (r1_tarski(A_199, k3_orders_2('#skF_2', '#skF_5', C_200)) | ~r2_hidden('#skF_1'(A_199, k3_orders_2('#skF_2', '#skF_5', C_200)), '#skF_5') | ~r2_orders_2('#skF_2', '#skF_1'(A_199, k3_orders_2('#skF_2', '#skF_5', C_200)), C_200) | ~m1_subset_1(C_200, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_199, k3_orders_2('#skF_2', '#skF_5', C_200)), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_142, c_4])).
% 3.33/1.50  tff(c_623, plain, (~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_339, c_611])).
% 3.33/1.50  tff(c_637, plain, (~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_623])).
% 3.33/1.50  tff(c_638, plain, (~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_20, c_637])).
% 3.33/1.50  tff(c_641, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_638])).
% 3.33/1.50  tff(c_644, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_188, c_641])).
% 3.33/1.50  tff(c_653, plain, (r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_644])).
% 3.33/1.50  tff(c_655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_653])).
% 3.33/1.50  tff(c_656, plain, (~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5')), inference(splitRight, [status(thm)], [c_638])).
% 3.33/1.50  tff(c_660, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_206, c_656])).
% 3.33/1.50  tff(c_678, plain, (v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_24, c_28, c_660])).
% 3.33/1.50  tff(c_680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_38, c_678])).
% 3.33/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.50  
% 3.33/1.50  Inference rules
% 3.33/1.50  ----------------------
% 3.33/1.50  #Ref     : 0
% 3.33/1.50  #Sup     : 129
% 3.33/1.50  #Fact    : 0
% 3.33/1.50  #Define  : 0
% 3.33/1.50  #Split   : 2
% 3.33/1.50  #Chain   : 0
% 3.33/1.50  #Close   : 0
% 3.33/1.50  
% 3.33/1.50  Ordering : KBO
% 3.33/1.50  
% 3.33/1.50  Simplification rules
% 3.33/1.50  ----------------------
% 3.33/1.50  #Subsume      : 35
% 3.33/1.50  #Demod        : 136
% 3.33/1.50  #Tautology    : 8
% 3.33/1.50  #SimpNegUnit  : 22
% 3.33/1.50  #BackRed      : 0
% 3.33/1.50  
% 3.33/1.50  #Partial instantiations: 0
% 3.33/1.50  #Strategies tried      : 1
% 3.33/1.50  
% 3.33/1.50  Timing (in seconds)
% 3.33/1.50  ----------------------
% 3.33/1.50  Preprocessing        : 0.30
% 3.33/1.50  Parsing              : 0.17
% 3.33/1.50  CNF conversion       : 0.03
% 3.33/1.50  Main loop            : 0.43
% 3.33/1.50  Inferencing          : 0.16
% 3.33/1.50  Reduction            : 0.11
% 3.33/1.51  Demodulation         : 0.08
% 3.33/1.51  BG Simplification    : 0.02
% 3.33/1.51  Subsumption          : 0.11
% 3.33/1.51  Abstraction          : 0.02
% 3.33/1.51  MUC search           : 0.00
% 3.33/1.51  Cooper               : 0.00
% 3.33/1.51  Total                : 0.78
% 3.33/1.51  Index Insertion      : 0.00
% 3.53/1.51  Index Deletion       : 0.00
% 3.53/1.51  Index Matching       : 0.00
% 3.53/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
