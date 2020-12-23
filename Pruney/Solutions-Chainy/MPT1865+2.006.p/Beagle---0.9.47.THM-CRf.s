%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:18 EST 2020

% Result     : Theorem 20.23s
% Output     : CNFRefutation 20.33s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 204 expanded)
%              Number of leaves         :   29 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  206 ( 581 expanded)
%              Number of equality atoms :   27 (  51 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v4_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_97,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(A_68,B_69)
      | ~ m1_subset_1(A_68,k1_zfmisc_1(B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_105,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_52,c_97])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_1'(A_70,B_71),A_70)
      | r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_111,plain,(
    ! [A_6,B_71] :
      ( '#skF_1'(k1_tarski(A_6),B_71) = A_6
      | r1_tarski(k1_tarski(A_6),B_71) ) ),
    inference(resolution,[status(thm)],[c_106,c_8])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_125,plain,(
    ! [C_75,B_76,A_77] :
      ( r2_hidden(C_75,B_76)
      | ~ r2_hidden(C_75,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_214,plain,(
    ! [A_92,B_93,B_94] :
      ( r2_hidden('#skF_1'(A_92,B_93),B_94)
      | ~ r1_tarski(A_92,B_94)
      | r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_6,c_125])).

tff(c_231,plain,(
    ! [A_95,A_96,B_97] :
      ( A_95 = '#skF_1'(A_96,B_97)
      | ~ r1_tarski(A_96,k1_tarski(A_95))
      | r1_tarski(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_214,c_8])).

tff(c_241,plain,(
    ! [A_95,A_6,B_97] :
      ( A_95 = '#skF_1'(k1_tarski(A_6),B_97)
      | r1_tarski(k1_tarski(A_6),B_97)
      | '#skF_1'(k1_tarski(A_6),k1_tarski(A_95)) = A_6 ) ),
    inference(resolution,[status(thm)],[c_111,c_231])).

tff(c_46,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_tarski(A_14),B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_314,plain,(
    ! [A_114,B_115,B_116,B_117] :
      ( r2_hidden('#skF_1'(A_114,B_115),B_116)
      | ~ r1_tarski(B_117,B_116)
      | ~ r1_tarski(A_114,B_117)
      | r1_tarski(A_114,B_115) ) ),
    inference(resolution,[status(thm)],[c_214,c_2])).

tff(c_529,plain,(
    ! [A_144,B_145,B_146,A_147] :
      ( r2_hidden('#skF_1'(A_144,B_145),B_146)
      | ~ r1_tarski(A_144,k1_tarski(A_147))
      | r1_tarski(A_144,B_145)
      | ~ r2_hidden(A_147,B_146) ) ),
    inference(resolution,[status(thm)],[c_26,c_314])).

tff(c_45468,plain,(
    ! [A_17440,B_17441,B_17442,A_17443] :
      ( r2_hidden('#skF_1'(k1_tarski(A_17440),B_17441),B_17442)
      | r1_tarski(k1_tarski(A_17440),B_17441)
      | ~ r2_hidden(A_17443,B_17442)
      | ~ r2_hidden(A_17440,k1_tarski(A_17443)) ) ),
    inference(resolution,[status(thm)],[c_26,c_529])).

tff(c_45560,plain,(
    ! [A_17488,B_17489] :
      ( r2_hidden('#skF_1'(k1_tarski(A_17488),B_17489),'#skF_7')
      | r1_tarski(k1_tarski(A_17488),B_17489)
      | ~ r2_hidden(A_17488,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_46,c_45468])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45766,plain,(
    ! [A_17534] :
      ( r1_tarski(k1_tarski(A_17534),'#skF_7')
      | ~ r2_hidden(A_17534,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_45560,c_4])).

tff(c_45818,plain,(
    r1_tarski(k1_tarski('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_45766])).

tff(c_228,plain,(
    ! [A_92,B_93,B_2,B_94] :
      ( r2_hidden('#skF_1'(A_92,B_93),B_2)
      | ~ r1_tarski(B_94,B_2)
      | ~ r1_tarski(A_92,B_94)
      | r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_214,c_2])).

tff(c_46902,plain,(
    ! [A_18210,B_18211] :
      ( r2_hidden('#skF_1'(A_18210,B_18211),'#skF_7')
      | ~ r1_tarski(A_18210,k1_tarski('#skF_8'))
      | r1_tarski(A_18210,B_18211) ) ),
    inference(resolution,[status(thm)],[c_45818,c_228])).

tff(c_47102,plain,(
    ! [A_18256] :
      ( ~ r1_tarski(A_18256,k1_tarski('#skF_8'))
      | r1_tarski(A_18256,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46902,c_4])).

tff(c_47123,plain,(
    ! [A_6,A_95] :
      ( r1_tarski(k1_tarski(A_6),'#skF_7')
      | A_95 = '#skF_1'(k1_tarski(A_6),k1_tarski('#skF_8'))
      | '#skF_1'(k1_tarski(A_6),k1_tarski(A_95)) = A_6 ) ),
    inference(resolution,[status(thm)],[c_241,c_47102])).

tff(c_90243,plain,(
    ! [A_33121] :
      ( r1_tarski(k1_tarski(A_33121),'#skF_7')
      | '#skF_1'(k1_tarski(A_33121),k1_tarski('#skF_8')) = '#skF_8'
      | A_33121 != '#skF_8' ) ),
    inference(factorization,[status(thm),theory(equality)],[c_47123])).

tff(c_90360,plain,(
    ! [A_33121] :
      ( ~ r2_hidden('#skF_8',k1_tarski('#skF_8'))
      | r1_tarski(k1_tarski(A_33121),k1_tarski('#skF_8'))
      | r1_tarski(k1_tarski(A_33121),'#skF_7')
      | A_33121 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90243,c_4])).

tff(c_90560,plain,(
    ! [A_33188] :
      ( r1_tarski(k1_tarski(A_33188),k1_tarski('#skF_8'))
      | r1_tarski(k1_tarski(A_33188),'#skF_7')
      | A_33188 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_90360])).

tff(c_47100,plain,(
    ! [A_18210] :
      ( ~ r1_tarski(A_18210,k1_tarski('#skF_8'))
      | r1_tarski(A_18210,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46902,c_4])).

tff(c_90632,plain,(
    r1_tarski(k1_tarski('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_90560,c_47100])).

tff(c_45923,plain,(
    ! [B_17758] :
      ( r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_8'),B_17758)),'#skF_7')
      | r1_tarski(k1_tarski('#skF_8'),B_17758) ) ),
    inference(resolution,[status(thm)],[c_6,c_45766])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | ~ r1_tarski(k1_tarski(A_14),B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_46209,plain,(
    ! [B_17847] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_8'),B_17847),'#skF_7')
      | r1_tarski(k1_tarski('#skF_8'),B_17847) ) ),
    inference(resolution,[status(thm)],[c_45923,c_24])).

tff(c_47578,plain,(
    ! [B_18436,B_18437] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_8'),B_18436),B_18437)
      | ~ r1_tarski('#skF_7',B_18437)
      | r1_tarski(k1_tarski('#skF_8'),B_18436) ) ),
    inference(resolution,[status(thm)],[c_46209,c_2])).

tff(c_47827,plain,(
    ! [B_18437] :
      ( ~ r1_tarski('#skF_7',B_18437)
      | r1_tarski(k1_tarski('#skF_8'),B_18437) ) ),
    inference(resolution,[status(thm)],[c_47578,c_4])).

tff(c_54,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_50,plain,(
    v2_tex_2('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2903,plain,(
    ! [A_2972,B_2973,C_2974] :
      ( v4_pre_topc('#skF_4'(A_2972,B_2973,C_2974),A_2972)
      | ~ r1_tarski(C_2974,B_2973)
      | ~ m1_subset_1(C_2974,k1_zfmisc_1(u1_struct_0(A_2972)))
      | ~ v2_tex_2(B_2973,A_2972)
      | ~ m1_subset_1(B_2973,k1_zfmisc_1(u1_struct_0(A_2972)))
      | ~ l1_pre_topc(A_2972) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_23092,plain,(
    ! [A_10286,B_10287,A_10288] :
      ( v4_pre_topc('#skF_4'(A_10286,B_10287,A_10288),A_10286)
      | ~ r1_tarski(A_10288,B_10287)
      | ~ v2_tex_2(B_10287,A_10286)
      | ~ m1_subset_1(B_10287,k1_zfmisc_1(u1_struct_0(A_10286)))
      | ~ l1_pre_topc(A_10286)
      | ~ r1_tarski(A_10288,u1_struct_0(A_10286)) ) ),
    inference(resolution,[status(thm)],[c_30,c_2903])).

tff(c_23116,plain,(
    ! [A_10286,A_16,A_10288] :
      ( v4_pre_topc('#skF_4'(A_10286,A_16,A_10288),A_10286)
      | ~ r1_tarski(A_10288,A_16)
      | ~ v2_tex_2(A_16,A_10286)
      | ~ l1_pre_topc(A_10286)
      | ~ r1_tarski(A_10288,u1_struct_0(A_10286))
      | ~ r1_tarski(A_16,u1_struct_0(A_10286)) ) ),
    inference(resolution,[status(thm)],[c_30,c_23092])).

tff(c_22377,plain,(
    ! [A_9557,B_9558,C_9559] :
      ( k9_subset_1(u1_struct_0(A_9557),B_9558,'#skF_4'(A_9557,B_9558,C_9559)) = C_9559
      | ~ r1_tarski(C_9559,B_9558)
      | ~ m1_subset_1(C_9559,k1_zfmisc_1(u1_struct_0(A_9557)))
      | ~ v2_tex_2(B_9558,A_9557)
      | ~ m1_subset_1(B_9558,k1_zfmisc_1(u1_struct_0(A_9557)))
      | ~ l1_pre_topc(A_9557) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_23202,plain,(
    ! [A_10516,B_10517,A_10518] :
      ( k9_subset_1(u1_struct_0(A_10516),B_10517,'#skF_4'(A_10516,B_10517,A_10518)) = A_10518
      | ~ r1_tarski(A_10518,B_10517)
      | ~ v2_tex_2(B_10517,A_10516)
      | ~ m1_subset_1(B_10517,k1_zfmisc_1(u1_struct_0(A_10516)))
      | ~ l1_pre_topc(A_10516)
      | ~ r1_tarski(A_10518,u1_struct_0(A_10516)) ) ),
    inference(resolution,[status(thm)],[c_30,c_22377])).

tff(c_23223,plain,(
    ! [A_10518] :
      ( k9_subset_1(u1_struct_0('#skF_6'),'#skF_7','#skF_4'('#skF_6','#skF_7',A_10518)) = A_10518
      | ~ r1_tarski(A_10518,'#skF_7')
      | ~ v2_tex_2('#skF_7','#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ r1_tarski(A_10518,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_52,c_23202])).

tff(c_23229,plain,(
    ! [A_10518] :
      ( k9_subset_1(u1_struct_0('#skF_6'),'#skF_7','#skF_4'('#skF_6','#skF_7',A_10518)) = A_10518
      | ~ r1_tarski(A_10518,'#skF_7')
      | ~ r1_tarski(A_10518,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_23223])).

tff(c_21505,plain,(
    ! [A_9374,B_9375,C_9376] :
      ( m1_subset_1('#skF_4'(A_9374,B_9375,C_9376),k1_zfmisc_1(u1_struct_0(A_9374)))
      | ~ r1_tarski(C_9376,B_9375)
      | ~ m1_subset_1(C_9376,k1_zfmisc_1(u1_struct_0(A_9374)))
      | ~ v2_tex_2(B_9375,A_9374)
      | ~ m1_subset_1(B_9375,k1_zfmisc_1(u1_struct_0(A_9374)))
      | ~ l1_pre_topc(A_9374) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    ! [D_54] :
      ( k9_subset_1(u1_struct_0('#skF_6'),'#skF_7',D_54) != k1_tarski('#skF_8')
      | ~ v4_pre_topc(D_54,'#skF_6')
      | ~ m1_subset_1(D_54,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_21516,plain,(
    ! [B_9375,C_9376] :
      ( k9_subset_1(u1_struct_0('#skF_6'),'#skF_7','#skF_4'('#skF_6',B_9375,C_9376)) != k1_tarski('#skF_8')
      | ~ v4_pre_topc('#skF_4'('#skF_6',B_9375,C_9376),'#skF_6')
      | ~ r1_tarski(C_9376,B_9375)
      | ~ m1_subset_1(C_9376,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v2_tex_2(B_9375,'#skF_6')
      | ~ m1_subset_1(B_9375,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_21505,c_44])).

tff(c_24013,plain,(
    ! [B_11021,C_11022] :
      ( k9_subset_1(u1_struct_0('#skF_6'),'#skF_7','#skF_4'('#skF_6',B_11021,C_11022)) != k1_tarski('#skF_8')
      | ~ v4_pre_topc('#skF_4'('#skF_6',B_11021,C_11022),'#skF_6')
      | ~ r1_tarski(C_11022,B_11021)
      | ~ m1_subset_1(C_11022,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v2_tex_2(B_11021,'#skF_6')
      | ~ m1_subset_1(B_11021,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_21516])).

tff(c_24015,plain,(
    ! [A_10518] :
      ( k1_tarski('#skF_8') != A_10518
      | ~ v4_pre_topc('#skF_4'('#skF_6','#skF_7',A_10518),'#skF_6')
      | ~ r1_tarski(A_10518,'#skF_7')
      | ~ m1_subset_1(A_10518,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v2_tex_2('#skF_7','#skF_6')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r1_tarski(A_10518,'#skF_7')
      | ~ r1_tarski(A_10518,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23229,c_24013])).

tff(c_93964,plain,(
    ! [A_39491] :
      ( k1_tarski('#skF_8') != A_39491
      | ~ v4_pre_topc('#skF_4'('#skF_6','#skF_7',A_39491),'#skF_6')
      | ~ m1_subset_1(A_39491,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r1_tarski(A_39491,'#skF_7')
      | ~ r1_tarski(A_39491,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_24015])).

tff(c_99639,plain,(
    ! [A_44440] :
      ( k1_tarski('#skF_8') != A_44440
      | ~ v4_pre_topc('#skF_4'('#skF_6','#skF_7',A_44440),'#skF_6')
      | ~ r1_tarski(A_44440,'#skF_7')
      | ~ r1_tarski(A_44440,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_30,c_93964])).

tff(c_99647,plain,(
    ! [A_10288] :
      ( k1_tarski('#skF_8') != A_10288
      | ~ r1_tarski(A_10288,'#skF_7')
      | ~ v2_tex_2('#skF_7','#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ r1_tarski(A_10288,u1_struct_0('#skF_6'))
      | ~ r1_tarski('#skF_7',u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_23116,c_99639])).

tff(c_99749,plain,(
    ! [A_44621] :
      ( k1_tarski('#skF_8') != A_44621
      | ~ r1_tarski(A_44621,'#skF_7')
      | ~ r1_tarski(A_44621,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_54,c_50,c_99647])).

tff(c_99770,plain,
    ( ~ r1_tarski(k1_tarski('#skF_8'),'#skF_7')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_47827,c_99749])).

tff(c_99830,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_90632,c_99770])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:26:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.23/10.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.23/10.32  
% 20.23/10.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.23/10.32  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_5
% 20.23/10.32  
% 20.23/10.32  %Foreground sorts:
% 20.23/10.32  
% 20.23/10.32  
% 20.23/10.32  %Background operators:
% 20.23/10.32  
% 20.23/10.32  
% 20.23/10.32  %Foreground operators:
% 20.23/10.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.23/10.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.23/10.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 20.23/10.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 20.23/10.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 20.23/10.32  tff('#skF_7', type, '#skF_7': $i).
% 20.23/10.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 20.23/10.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.23/10.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.23/10.32  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 20.23/10.32  tff('#skF_6', type, '#skF_6': $i).
% 20.23/10.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 20.23/10.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.23/10.32  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 20.23/10.32  tff('#skF_8', type, '#skF_8': $i).
% 20.23/10.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.23/10.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.23/10.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 20.23/10.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 20.23/10.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.23/10.32  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 20.23/10.32  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 20.23/10.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.23/10.32  
% 20.33/10.34  tff(f_94, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tex_2)).
% 20.33/10.34  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 20.33/10.34  tff(f_39, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 20.33/10.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 20.33/10.34  tff(f_47, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 20.33/10.34  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 20.33/10.34  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 20.33/10.34  tff(c_97, plain, (![A_68, B_69]: (r1_tarski(A_68, B_69) | ~m1_subset_1(A_68, k1_zfmisc_1(B_69)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.33/10.34  tff(c_105, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_97])).
% 20.33/10.34  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 20.33/10.34  tff(c_106, plain, (![A_70, B_71]: (r2_hidden('#skF_1'(A_70, B_71), A_70) | r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.33/10.34  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 20.33/10.34  tff(c_111, plain, (![A_6, B_71]: ('#skF_1'(k1_tarski(A_6), B_71)=A_6 | r1_tarski(k1_tarski(A_6), B_71))), inference(resolution, [status(thm)], [c_106, c_8])).
% 20.33/10.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.33/10.34  tff(c_125, plain, (![C_75, B_76, A_77]: (r2_hidden(C_75, B_76) | ~r2_hidden(C_75, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.33/10.34  tff(c_214, plain, (![A_92, B_93, B_94]: (r2_hidden('#skF_1'(A_92, B_93), B_94) | ~r1_tarski(A_92, B_94) | r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_6, c_125])).
% 20.33/10.34  tff(c_231, plain, (![A_95, A_96, B_97]: (A_95='#skF_1'(A_96, B_97) | ~r1_tarski(A_96, k1_tarski(A_95)) | r1_tarski(A_96, B_97))), inference(resolution, [status(thm)], [c_214, c_8])).
% 20.33/10.34  tff(c_241, plain, (![A_95, A_6, B_97]: (A_95='#skF_1'(k1_tarski(A_6), B_97) | r1_tarski(k1_tarski(A_6), B_97) | '#skF_1'(k1_tarski(A_6), k1_tarski(A_95))=A_6)), inference(resolution, [status(thm)], [c_111, c_231])).
% 20.33/10.34  tff(c_46, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_94])).
% 20.33/10.34  tff(c_26, plain, (![A_14, B_15]: (r1_tarski(k1_tarski(A_14), B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.33/10.34  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.33/10.34  tff(c_314, plain, (![A_114, B_115, B_116, B_117]: (r2_hidden('#skF_1'(A_114, B_115), B_116) | ~r1_tarski(B_117, B_116) | ~r1_tarski(A_114, B_117) | r1_tarski(A_114, B_115))), inference(resolution, [status(thm)], [c_214, c_2])).
% 20.33/10.34  tff(c_529, plain, (![A_144, B_145, B_146, A_147]: (r2_hidden('#skF_1'(A_144, B_145), B_146) | ~r1_tarski(A_144, k1_tarski(A_147)) | r1_tarski(A_144, B_145) | ~r2_hidden(A_147, B_146))), inference(resolution, [status(thm)], [c_26, c_314])).
% 20.33/10.34  tff(c_45468, plain, (![A_17440, B_17441, B_17442, A_17443]: (r2_hidden('#skF_1'(k1_tarski(A_17440), B_17441), B_17442) | r1_tarski(k1_tarski(A_17440), B_17441) | ~r2_hidden(A_17443, B_17442) | ~r2_hidden(A_17440, k1_tarski(A_17443)))), inference(resolution, [status(thm)], [c_26, c_529])).
% 20.33/10.34  tff(c_45560, plain, (![A_17488, B_17489]: (r2_hidden('#skF_1'(k1_tarski(A_17488), B_17489), '#skF_7') | r1_tarski(k1_tarski(A_17488), B_17489) | ~r2_hidden(A_17488, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_46, c_45468])).
% 20.33/10.34  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.33/10.34  tff(c_45766, plain, (![A_17534]: (r1_tarski(k1_tarski(A_17534), '#skF_7') | ~r2_hidden(A_17534, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_45560, c_4])).
% 20.33/10.34  tff(c_45818, plain, (r1_tarski(k1_tarski('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_10, c_45766])).
% 20.33/10.34  tff(c_228, plain, (![A_92, B_93, B_2, B_94]: (r2_hidden('#skF_1'(A_92, B_93), B_2) | ~r1_tarski(B_94, B_2) | ~r1_tarski(A_92, B_94) | r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_214, c_2])).
% 20.33/10.34  tff(c_46902, plain, (![A_18210, B_18211]: (r2_hidden('#skF_1'(A_18210, B_18211), '#skF_7') | ~r1_tarski(A_18210, k1_tarski('#skF_8')) | r1_tarski(A_18210, B_18211))), inference(resolution, [status(thm)], [c_45818, c_228])).
% 20.33/10.34  tff(c_47102, plain, (![A_18256]: (~r1_tarski(A_18256, k1_tarski('#skF_8')) | r1_tarski(A_18256, '#skF_7'))), inference(resolution, [status(thm)], [c_46902, c_4])).
% 20.33/10.34  tff(c_47123, plain, (![A_6, A_95]: (r1_tarski(k1_tarski(A_6), '#skF_7') | A_95='#skF_1'(k1_tarski(A_6), k1_tarski('#skF_8')) | '#skF_1'(k1_tarski(A_6), k1_tarski(A_95))=A_6)), inference(resolution, [status(thm)], [c_241, c_47102])).
% 20.33/10.34  tff(c_90243, plain, (![A_33121]: (r1_tarski(k1_tarski(A_33121), '#skF_7') | '#skF_1'(k1_tarski(A_33121), k1_tarski('#skF_8'))='#skF_8' | A_33121!='#skF_8')), inference(factorization, [status(thm), theory('equality')], [c_47123])).
% 20.33/10.34  tff(c_90360, plain, (![A_33121]: (~r2_hidden('#skF_8', k1_tarski('#skF_8')) | r1_tarski(k1_tarski(A_33121), k1_tarski('#skF_8')) | r1_tarski(k1_tarski(A_33121), '#skF_7') | A_33121!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_90243, c_4])).
% 20.33/10.34  tff(c_90560, plain, (![A_33188]: (r1_tarski(k1_tarski(A_33188), k1_tarski('#skF_8')) | r1_tarski(k1_tarski(A_33188), '#skF_7') | A_33188!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_90360])).
% 20.33/10.34  tff(c_47100, plain, (![A_18210]: (~r1_tarski(A_18210, k1_tarski('#skF_8')) | r1_tarski(A_18210, '#skF_7'))), inference(resolution, [status(thm)], [c_46902, c_4])).
% 20.33/10.34  tff(c_90632, plain, (r1_tarski(k1_tarski('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_90560, c_47100])).
% 20.33/10.34  tff(c_45923, plain, (![B_17758]: (r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_8'), B_17758)), '#skF_7') | r1_tarski(k1_tarski('#skF_8'), B_17758))), inference(resolution, [status(thm)], [c_6, c_45766])).
% 20.33/10.34  tff(c_24, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | ~r1_tarski(k1_tarski(A_14), B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.33/10.34  tff(c_46209, plain, (![B_17847]: (r2_hidden('#skF_1'(k1_tarski('#skF_8'), B_17847), '#skF_7') | r1_tarski(k1_tarski('#skF_8'), B_17847))), inference(resolution, [status(thm)], [c_45923, c_24])).
% 20.33/10.34  tff(c_47578, plain, (![B_18436, B_18437]: (r2_hidden('#skF_1'(k1_tarski('#skF_8'), B_18436), B_18437) | ~r1_tarski('#skF_7', B_18437) | r1_tarski(k1_tarski('#skF_8'), B_18436))), inference(resolution, [status(thm)], [c_46209, c_2])).
% 20.33/10.34  tff(c_47827, plain, (![B_18437]: (~r1_tarski('#skF_7', B_18437) | r1_tarski(k1_tarski('#skF_8'), B_18437))), inference(resolution, [status(thm)], [c_47578, c_4])).
% 20.33/10.34  tff(c_54, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_94])).
% 20.33/10.34  tff(c_50, plain, (v2_tex_2('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_94])).
% 20.33/10.34  tff(c_30, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.33/10.34  tff(c_2903, plain, (![A_2972, B_2973, C_2974]: (v4_pre_topc('#skF_4'(A_2972, B_2973, C_2974), A_2972) | ~r1_tarski(C_2974, B_2973) | ~m1_subset_1(C_2974, k1_zfmisc_1(u1_struct_0(A_2972))) | ~v2_tex_2(B_2973, A_2972) | ~m1_subset_1(B_2973, k1_zfmisc_1(u1_struct_0(A_2972))) | ~l1_pre_topc(A_2972))), inference(cnfTransformation, [status(thm)], [f_72])).
% 20.33/10.34  tff(c_23092, plain, (![A_10286, B_10287, A_10288]: (v4_pre_topc('#skF_4'(A_10286, B_10287, A_10288), A_10286) | ~r1_tarski(A_10288, B_10287) | ~v2_tex_2(B_10287, A_10286) | ~m1_subset_1(B_10287, k1_zfmisc_1(u1_struct_0(A_10286))) | ~l1_pre_topc(A_10286) | ~r1_tarski(A_10288, u1_struct_0(A_10286)))), inference(resolution, [status(thm)], [c_30, c_2903])).
% 20.33/10.34  tff(c_23116, plain, (![A_10286, A_16, A_10288]: (v4_pre_topc('#skF_4'(A_10286, A_16, A_10288), A_10286) | ~r1_tarski(A_10288, A_16) | ~v2_tex_2(A_16, A_10286) | ~l1_pre_topc(A_10286) | ~r1_tarski(A_10288, u1_struct_0(A_10286)) | ~r1_tarski(A_16, u1_struct_0(A_10286)))), inference(resolution, [status(thm)], [c_30, c_23092])).
% 20.33/10.34  tff(c_22377, plain, (![A_9557, B_9558, C_9559]: (k9_subset_1(u1_struct_0(A_9557), B_9558, '#skF_4'(A_9557, B_9558, C_9559))=C_9559 | ~r1_tarski(C_9559, B_9558) | ~m1_subset_1(C_9559, k1_zfmisc_1(u1_struct_0(A_9557))) | ~v2_tex_2(B_9558, A_9557) | ~m1_subset_1(B_9558, k1_zfmisc_1(u1_struct_0(A_9557))) | ~l1_pre_topc(A_9557))), inference(cnfTransformation, [status(thm)], [f_72])).
% 20.33/10.34  tff(c_23202, plain, (![A_10516, B_10517, A_10518]: (k9_subset_1(u1_struct_0(A_10516), B_10517, '#skF_4'(A_10516, B_10517, A_10518))=A_10518 | ~r1_tarski(A_10518, B_10517) | ~v2_tex_2(B_10517, A_10516) | ~m1_subset_1(B_10517, k1_zfmisc_1(u1_struct_0(A_10516))) | ~l1_pre_topc(A_10516) | ~r1_tarski(A_10518, u1_struct_0(A_10516)))), inference(resolution, [status(thm)], [c_30, c_22377])).
% 20.33/10.34  tff(c_23223, plain, (![A_10518]: (k9_subset_1(u1_struct_0('#skF_6'), '#skF_7', '#skF_4'('#skF_6', '#skF_7', A_10518))=A_10518 | ~r1_tarski(A_10518, '#skF_7') | ~v2_tex_2('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6') | ~r1_tarski(A_10518, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_52, c_23202])).
% 20.33/10.34  tff(c_23229, plain, (![A_10518]: (k9_subset_1(u1_struct_0('#skF_6'), '#skF_7', '#skF_4'('#skF_6', '#skF_7', A_10518))=A_10518 | ~r1_tarski(A_10518, '#skF_7') | ~r1_tarski(A_10518, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_23223])).
% 20.33/10.34  tff(c_21505, plain, (![A_9374, B_9375, C_9376]: (m1_subset_1('#skF_4'(A_9374, B_9375, C_9376), k1_zfmisc_1(u1_struct_0(A_9374))) | ~r1_tarski(C_9376, B_9375) | ~m1_subset_1(C_9376, k1_zfmisc_1(u1_struct_0(A_9374))) | ~v2_tex_2(B_9375, A_9374) | ~m1_subset_1(B_9375, k1_zfmisc_1(u1_struct_0(A_9374))) | ~l1_pre_topc(A_9374))), inference(cnfTransformation, [status(thm)], [f_72])).
% 20.33/10.34  tff(c_44, plain, (![D_54]: (k9_subset_1(u1_struct_0('#skF_6'), '#skF_7', D_54)!=k1_tarski('#skF_8') | ~v4_pre_topc(D_54, '#skF_6') | ~m1_subset_1(D_54, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 20.33/10.34  tff(c_21516, plain, (![B_9375, C_9376]: (k9_subset_1(u1_struct_0('#skF_6'), '#skF_7', '#skF_4'('#skF_6', B_9375, C_9376))!=k1_tarski('#skF_8') | ~v4_pre_topc('#skF_4'('#skF_6', B_9375, C_9376), '#skF_6') | ~r1_tarski(C_9376, B_9375) | ~m1_subset_1(C_9376, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v2_tex_2(B_9375, '#skF_6') | ~m1_subset_1(B_9375, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_21505, c_44])).
% 20.33/10.34  tff(c_24013, plain, (![B_11021, C_11022]: (k9_subset_1(u1_struct_0('#skF_6'), '#skF_7', '#skF_4'('#skF_6', B_11021, C_11022))!=k1_tarski('#skF_8') | ~v4_pre_topc('#skF_4'('#skF_6', B_11021, C_11022), '#skF_6') | ~r1_tarski(C_11022, B_11021) | ~m1_subset_1(C_11022, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v2_tex_2(B_11021, '#skF_6') | ~m1_subset_1(B_11021, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_21516])).
% 20.33/10.34  tff(c_24015, plain, (![A_10518]: (k1_tarski('#skF_8')!=A_10518 | ~v4_pre_topc('#skF_4'('#skF_6', '#skF_7', A_10518), '#skF_6') | ~r1_tarski(A_10518, '#skF_7') | ~m1_subset_1(A_10518, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v2_tex_2('#skF_7', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r1_tarski(A_10518, '#skF_7') | ~r1_tarski(A_10518, u1_struct_0('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_23229, c_24013])).
% 20.33/10.34  tff(c_93964, plain, (![A_39491]: (k1_tarski('#skF_8')!=A_39491 | ~v4_pre_topc('#skF_4'('#skF_6', '#skF_7', A_39491), '#skF_6') | ~m1_subset_1(A_39491, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r1_tarski(A_39491, '#skF_7') | ~r1_tarski(A_39491, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_24015])).
% 20.33/10.34  tff(c_99639, plain, (![A_44440]: (k1_tarski('#skF_8')!=A_44440 | ~v4_pre_topc('#skF_4'('#skF_6', '#skF_7', A_44440), '#skF_6') | ~r1_tarski(A_44440, '#skF_7') | ~r1_tarski(A_44440, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_30, c_93964])).
% 20.33/10.34  tff(c_99647, plain, (![A_10288]: (k1_tarski('#skF_8')!=A_10288 | ~r1_tarski(A_10288, '#skF_7') | ~v2_tex_2('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6') | ~r1_tarski(A_10288, u1_struct_0('#skF_6')) | ~r1_tarski('#skF_7', u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_23116, c_99639])).
% 20.33/10.34  tff(c_99749, plain, (![A_44621]: (k1_tarski('#skF_8')!=A_44621 | ~r1_tarski(A_44621, '#skF_7') | ~r1_tarski(A_44621, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_54, c_50, c_99647])).
% 20.33/10.34  tff(c_99770, plain, (~r1_tarski(k1_tarski('#skF_8'), '#skF_7') | ~r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_47827, c_99749])).
% 20.33/10.34  tff(c_99830, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_90632, c_99770])).
% 20.33/10.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.33/10.34  
% 20.33/10.34  Inference rules
% 20.33/10.34  ----------------------
% 20.33/10.34  #Ref     : 1
% 20.33/10.34  #Sup     : 15867
% 20.33/10.34  #Fact    : 23
% 20.33/10.34  #Define  : 0
% 20.33/10.34  #Split   : 16
% 20.33/10.34  #Chain   : 0
% 20.33/10.34  #Close   : 0
% 20.33/10.34  
% 20.33/10.34  Ordering : KBO
% 20.33/10.34  
% 20.33/10.34  Simplification rules
% 20.33/10.34  ----------------------
% 20.33/10.34  #Subsume      : 3782
% 20.33/10.34  #Demod        : 1835
% 20.33/10.34  #Tautology    : 1619
% 20.33/10.34  #SimpNegUnit  : 35
% 20.33/10.34  #BackRed      : 0
% 20.33/10.34  
% 20.33/10.34  #Partial instantiations: 28056
% 20.33/10.34  #Strategies tried      : 1
% 20.33/10.34  
% 20.33/10.34  Timing (in seconds)
% 20.33/10.34  ----------------------
% 20.33/10.34  Preprocessing        : 0.32
% 20.33/10.34  Parsing              : 0.16
% 20.33/10.34  CNF conversion       : 0.03
% 20.33/10.34  Main loop            : 9.24
% 20.33/10.34  Inferencing          : 2.12
% 20.33/10.34  Reduction            : 1.81
% 20.33/10.34  Demodulation         : 1.25
% 20.33/10.34  BG Simplification    : 0.34
% 20.33/10.34  Subsumption          : 4.42
% 20.33/10.34  Abstraction          : 0.41
% 20.33/10.34  MUC search           : 0.00
% 20.33/10.34  Cooper               : 0.00
% 20.33/10.34  Total                : 9.60
% 20.33/10.34  Index Insertion      : 0.00
% 20.33/10.34  Index Deletion       : 0.00
% 20.33/10.34  Index Matching       : 0.00
% 20.33/10.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
