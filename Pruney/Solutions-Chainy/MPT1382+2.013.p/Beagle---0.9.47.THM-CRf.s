%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:09 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 143 expanded)
%              Number of leaves         :   27 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  171 ( 565 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( m1_connsp_2(C,A,B)
                    & ! [D] :
                        ( ( ~ v1_xboole_0(D)
                          & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                       => ~ ( m1_connsp_2(D,A,B)
                            & v3_pre_topc(D,A)
                            & r1_tarski(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(c_26,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_56,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_64,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_56])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_209,plain,(
    ! [B_90,A_91,C_92] :
      ( r2_hidden(B_90,k1_tops_1(A_91,C_92))
      | ~ m1_connsp_2(C_92,A_91,B_90)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m1_subset_1(B_90,u1_struct_0(A_91))
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_215,plain,(
    ! [B_90,A_91,A_8] :
      ( r2_hidden(B_90,k1_tops_1(A_91,A_8))
      | ~ m1_connsp_2(A_8,A_91,B_90)
      | ~ m1_subset_1(B_90,u1_struct_0(A_91))
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91)
      | ~ r1_tarski(A_8,u1_struct_0(A_91)) ) ),
    inference(resolution,[status(thm)],[c_10,c_209])).

tff(c_214,plain,(
    ! [B_90] :
      ( r2_hidden(B_90,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_90)
      | ~ m1_subset_1(B_90,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_209])).

tff(c_218,plain,(
    ! [B_90] :
      ( r2_hidden(B_90,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_90)
      | ~ m1_subset_1(B_90,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_214])).

tff(c_220,plain,(
    ! [B_93] :
      ( r2_hidden(B_93,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_93)
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_218])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_230,plain,(
    ! [B_93] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_93)
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_220,c_2])).

tff(c_231,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_70,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tops_1(A_56,B_57),B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_75,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_70])).

tff(c_79,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_75])).

tff(c_133,plain,(
    ! [A_66,B_67] :
      ( v3_pre_topc(k1_tops_1(A_66,B_67),A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_138,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_133])).

tff(c_142,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_138])).

tff(c_66,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_tarski(A_53,C_54)
      | ~ r1_tarski(B_55,C_54)
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [A_53] :
      ( r1_tarski(A_53,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_53,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_66])).

tff(c_256,plain,(
    ! [B_104,A_105,C_106] :
      ( m1_connsp_2(B_104,A_105,C_106)
      | ~ r2_hidden(C_106,B_104)
      | ~ v3_pre_topc(B_104,A_105)
      | ~ m1_subset_1(C_106,u1_struct_0(A_105))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_258,plain,(
    ! [B_104] :
      ( m1_connsp_2(B_104,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_104)
      | ~ v3_pre_topc(B_104,'#skF_2')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_256])).

tff(c_261,plain,(
    ! [B_104] :
      ( m1_connsp_2(B_104,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_104)
      | ~ v3_pre_topc(B_104,'#skF_2')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_258])).

tff(c_263,plain,(
    ! [B_107] :
      ( m1_connsp_2(B_107,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_107)
      | ~ v3_pre_topc(B_107,'#skF_2')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_261])).

tff(c_274,plain,(
    ! [A_108] :
      ( m1_connsp_2(A_108,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',A_108)
      | ~ v3_pre_topc(A_108,'#skF_2')
      | ~ r1_tarski(A_108,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_263])).

tff(c_298,plain,(
    ! [A_109] :
      ( m1_connsp_2(A_109,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',A_109)
      | ~ v3_pre_topc(A_109,'#skF_2')
      | ~ r1_tarski(A_109,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_69,c_274])).

tff(c_44,plain,(
    ! [D_50] :
      ( ~ r1_tarski(D_50,'#skF_4')
      | ~ v3_pre_topc(D_50,'#skF_2')
      | ~ m1_connsp_2(D_50,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(D_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_88,plain,(
    ! [A_60] :
      ( ~ r1_tarski(A_60,'#skF_4')
      | ~ v3_pre_topc(A_60,'#skF_2')
      | ~ m1_connsp_2(A_60,'#skF_2','#skF_3')
      | v1_xboole_0(A_60)
      | ~ r1_tarski(A_60,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_44])).

tff(c_95,plain,(
    ! [A_53] :
      ( ~ v3_pre_topc(A_53,'#skF_2')
      | ~ m1_connsp_2(A_53,'#skF_2','#skF_3')
      | v1_xboole_0(A_53)
      | ~ r1_tarski(A_53,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_69,c_88])).

tff(c_315,plain,(
    ! [A_110] :
      ( v1_xboole_0(A_110)
      | ~ r2_hidden('#skF_3',A_110)
      | ~ v3_pre_topc(A_110,'#skF_2')
      | ~ r1_tarski(A_110,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_298,c_95])).

tff(c_322,plain,
    ( v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_315])).

tff(c_328,plain,
    ( v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_322])).

tff(c_329,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_328])).

tff(c_357,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_215,c_329])).

tff(c_363,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_34,c_32,c_30,c_26,c_357])).

tff(c_365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_363])).

tff(c_368,plain,(
    ! [B_112] :
      ( ~ m1_connsp_2('#skF_4','#skF_2',B_112)
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_371,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_368])).

tff(c_375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:26:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.34  
% 2.65/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.35  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.65/1.35  
% 2.65/1.35  %Foreground sorts:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Background operators:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Foreground operators:
% 2.65/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.65/1.35  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.65/1.35  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.65/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.65/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.35  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.65/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.65/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.65/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.65/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.35  
% 2.65/1.36  tff(f_136, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 2.65/1.36  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.65/1.36  tff(f_73, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.65/1.36  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.65/1.36  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.65/1.36  tff(f_49, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.65/1.36  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.65/1.36  tff(f_106, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 2.65/1.36  tff(c_26, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.65/1.36  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.65/1.36  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.65/1.36  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.65/1.36  tff(c_56, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.65/1.36  tff(c_64, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_56])).
% 2.65/1.36  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.65/1.36  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.65/1.36  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.65/1.36  tff(c_209, plain, (![B_90, A_91, C_92]: (r2_hidden(B_90, k1_tops_1(A_91, C_92)) | ~m1_connsp_2(C_92, A_91, B_90) | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~m1_subset_1(B_90, u1_struct_0(A_91)) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.65/1.36  tff(c_215, plain, (![B_90, A_91, A_8]: (r2_hidden(B_90, k1_tops_1(A_91, A_8)) | ~m1_connsp_2(A_8, A_91, B_90) | ~m1_subset_1(B_90, u1_struct_0(A_91)) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91) | ~r1_tarski(A_8, u1_struct_0(A_91)))), inference(resolution, [status(thm)], [c_10, c_209])).
% 2.65/1.36  tff(c_214, plain, (![B_90]: (r2_hidden(B_90, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_90) | ~m1_subset_1(B_90, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_209])).
% 2.65/1.36  tff(c_218, plain, (![B_90]: (r2_hidden(B_90, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_90) | ~m1_subset_1(B_90, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_214])).
% 2.65/1.36  tff(c_220, plain, (![B_93]: (r2_hidden(B_93, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_93) | ~m1_subset_1(B_93, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_218])).
% 2.65/1.36  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.36  tff(c_230, plain, (![B_93]: (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_93) | ~m1_subset_1(B_93, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_220, c_2])).
% 2.65/1.36  tff(c_231, plain, (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_230])).
% 2.65/1.36  tff(c_70, plain, (![A_56, B_57]: (r1_tarski(k1_tops_1(A_56, B_57), B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.65/1.36  tff(c_75, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_70])).
% 2.65/1.36  tff(c_79, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_75])).
% 2.65/1.36  tff(c_133, plain, (![A_66, B_67]: (v3_pre_topc(k1_tops_1(A_66, B_67), A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.65/1.36  tff(c_138, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_133])).
% 2.65/1.36  tff(c_142, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_138])).
% 2.65/1.36  tff(c_66, plain, (![A_53, C_54, B_55]: (r1_tarski(A_53, C_54) | ~r1_tarski(B_55, C_54) | ~r1_tarski(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.65/1.36  tff(c_69, plain, (![A_53]: (r1_tarski(A_53, u1_struct_0('#skF_2')) | ~r1_tarski(A_53, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_66])).
% 2.65/1.36  tff(c_256, plain, (![B_104, A_105, C_106]: (m1_connsp_2(B_104, A_105, C_106) | ~r2_hidden(C_106, B_104) | ~v3_pre_topc(B_104, A_105) | ~m1_subset_1(C_106, u1_struct_0(A_105)) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.65/1.36  tff(c_258, plain, (![B_104]: (m1_connsp_2(B_104, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_104) | ~v3_pre_topc(B_104, '#skF_2') | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_256])).
% 2.65/1.36  tff(c_261, plain, (![B_104]: (m1_connsp_2(B_104, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_104) | ~v3_pre_topc(B_104, '#skF_2') | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_258])).
% 2.65/1.36  tff(c_263, plain, (![B_107]: (m1_connsp_2(B_107, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_107) | ~v3_pre_topc(B_107, '#skF_2') | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_261])).
% 2.65/1.36  tff(c_274, plain, (![A_108]: (m1_connsp_2(A_108, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', A_108) | ~v3_pre_topc(A_108, '#skF_2') | ~r1_tarski(A_108, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_263])).
% 2.65/1.36  tff(c_298, plain, (![A_109]: (m1_connsp_2(A_109, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', A_109) | ~v3_pre_topc(A_109, '#skF_2') | ~r1_tarski(A_109, '#skF_4'))), inference(resolution, [status(thm)], [c_69, c_274])).
% 2.65/1.36  tff(c_44, plain, (![D_50]: (~r1_tarski(D_50, '#skF_4') | ~v3_pre_topc(D_50, '#skF_2') | ~m1_connsp_2(D_50, '#skF_2', '#skF_3') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(D_50))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.65/1.36  tff(c_88, plain, (![A_60]: (~r1_tarski(A_60, '#skF_4') | ~v3_pre_topc(A_60, '#skF_2') | ~m1_connsp_2(A_60, '#skF_2', '#skF_3') | v1_xboole_0(A_60) | ~r1_tarski(A_60, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_44])).
% 2.65/1.36  tff(c_95, plain, (![A_53]: (~v3_pre_topc(A_53, '#skF_2') | ~m1_connsp_2(A_53, '#skF_2', '#skF_3') | v1_xboole_0(A_53) | ~r1_tarski(A_53, '#skF_4'))), inference(resolution, [status(thm)], [c_69, c_88])).
% 2.65/1.36  tff(c_315, plain, (![A_110]: (v1_xboole_0(A_110) | ~r2_hidden('#skF_3', A_110) | ~v3_pre_topc(A_110, '#skF_2') | ~r1_tarski(A_110, '#skF_4'))), inference(resolution, [status(thm)], [c_298, c_95])).
% 2.65/1.36  tff(c_322, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_142, c_315])).
% 2.65/1.36  tff(c_328, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_322])).
% 2.65/1.36  tff(c_329, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_231, c_328])).
% 2.65/1.36  tff(c_357, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_215, c_329])).
% 2.65/1.36  tff(c_363, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_34, c_32, c_30, c_26, c_357])).
% 2.65/1.36  tff(c_365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_363])).
% 2.65/1.36  tff(c_368, plain, (![B_112]: (~m1_connsp_2('#skF_4', '#skF_2', B_112) | ~m1_subset_1(B_112, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_230])).
% 2.65/1.36  tff(c_371, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_368])).
% 2.65/1.36  tff(c_375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_371])).
% 2.65/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.36  
% 2.65/1.36  Inference rules
% 2.65/1.36  ----------------------
% 2.65/1.36  #Ref     : 0
% 2.65/1.36  #Sup     : 67
% 2.65/1.36  #Fact    : 0
% 2.65/1.36  #Define  : 0
% 2.65/1.36  #Split   : 3
% 2.65/1.36  #Chain   : 0
% 2.65/1.36  #Close   : 0
% 2.65/1.36  
% 2.65/1.36  Ordering : KBO
% 2.65/1.36  
% 2.65/1.36  Simplification rules
% 2.65/1.36  ----------------------
% 2.65/1.36  #Subsume      : 14
% 2.65/1.36  #Demod        : 43
% 2.65/1.36  #Tautology    : 6
% 2.65/1.36  #SimpNegUnit  : 10
% 2.65/1.36  #BackRed      : 0
% 2.65/1.36  
% 2.65/1.36  #Partial instantiations: 0
% 2.65/1.36  #Strategies tried      : 1
% 2.65/1.36  
% 2.65/1.37  Timing (in seconds)
% 2.65/1.37  ----------------------
% 2.65/1.37  Preprocessing        : 0.30
% 2.65/1.37  Parsing              : 0.17
% 2.65/1.37  CNF conversion       : 0.02
% 2.65/1.37  Main loop            : 0.28
% 2.65/1.37  Inferencing          : 0.11
% 2.65/1.37  Reduction            : 0.07
% 2.65/1.37  Demodulation         : 0.05
% 2.65/1.37  BG Simplification    : 0.02
% 2.65/1.37  Subsumption          : 0.06
% 2.65/1.37  Abstraction          : 0.01
% 2.65/1.37  MUC search           : 0.00
% 2.65/1.37  Cooper               : 0.00
% 2.65/1.37  Total                : 0.62
% 2.65/1.37  Index Insertion      : 0.00
% 2.65/1.37  Index Deletion       : 0.00
% 2.65/1.37  Index Matching       : 0.00
% 2.65/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
