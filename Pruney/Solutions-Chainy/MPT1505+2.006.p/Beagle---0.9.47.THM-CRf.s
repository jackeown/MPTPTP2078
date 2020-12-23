%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:45 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 402 expanded)
%              Number of leaves         :   39 ( 157 expanded)
%              Depth                    :   18
%              Number of atoms          :  431 (1784 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff(a_2_2_lattice3,type,(
    a_2_2_lattice3: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_183,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( r2_hidden(B,C)
               => ( r3_lattices(A,B,k15_lattice3(A,C))
                  & r3_lattices(A,k16_lattice3(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k16_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

tff(f_151,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( B = k16_lattice3(A,C)
            <=> ( r3_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r3_lattice3(A,D,C)
                     => r3_lattices(A,D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r3_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

tff(f_47,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_163,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] : k15_lattice3(A,B) = k16_lattice3(A,a_2_2_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & v4_lattice3(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_2_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r4_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r4_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_lattices(A,B,C)
      <=> r1_lattices(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_64,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_68,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_66,plain,(
    v4_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_36,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k16_lattice3(A_49,B_50),u1_struct_0(A_49))
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1123,plain,(
    ! [A_325,C_326] :
      ( r3_lattice3(A_325,k16_lattice3(A_325,C_326),C_326)
      | ~ m1_subset_1(k16_lattice3(A_325,C_326),u1_struct_0(A_325))
      | ~ l3_lattices(A_325)
      | ~ v4_lattice3(A_325)
      | ~ v10_lattices(A_325)
      | v2_struct_0(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1128,plain,(
    ! [A_49,B_50] :
      ( r3_lattice3(A_49,k16_lattice3(A_49,B_50),B_50)
      | ~ v4_lattice3(A_49)
      | ~ v10_lattices(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_36,c_1123])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_60,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1209,plain,(
    ! [A_348,B_349,D_350,C_351] :
      ( r1_lattices(A_348,B_349,D_350)
      | ~ r2_hidden(D_350,C_351)
      | ~ m1_subset_1(D_350,u1_struct_0(A_348))
      | ~ r3_lattice3(A_348,B_349,C_351)
      | ~ m1_subset_1(B_349,u1_struct_0(A_348))
      | ~ l3_lattices(A_348)
      | v2_struct_0(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1250,plain,(
    ! [A_358,B_359] :
      ( r1_lattices(A_358,B_359,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_358))
      | ~ r3_lattice3(A_358,B_359,'#skF_7')
      | ~ m1_subset_1(B_359,u1_struct_0(A_358))
      | ~ l3_lattices(A_358)
      | v2_struct_0(A_358) ) ),
    inference(resolution,[status(thm)],[c_60,c_1209])).

tff(c_1252,plain,(
    ! [B_359] :
      ( r1_lattices('#skF_5',B_359,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_359,'#skF_7')
      | ~ m1_subset_1(B_359,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_1250])).

tff(c_1255,plain,(
    ! [B_359] :
      ( r1_lattices('#skF_5',B_359,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_359,'#skF_7')
      | ~ m1_subset_1(B_359,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1252])).

tff(c_1257,plain,(
    ! [B_360] :
      ( r1_lattices('#skF_5',B_360,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_360,'#skF_7')
      | ~ m1_subset_1(B_360,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1255])).

tff(c_1277,plain,(
    ! [B_50] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5',B_50),'#skF_6')
      | ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5',B_50),'#skF_7')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_1257])).

tff(c_1299,plain,(
    ! [B_50] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5',B_50),'#skF_6')
      | ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5',B_50),'#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1277])).

tff(c_1310,plain,(
    ! [B_364] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5',B_364),'#skF_6')
      | ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5',B_364),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1299])).

tff(c_1314,plain,
    ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1128,c_1310])).

tff(c_1321,plain,
    ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_66,c_1314])).

tff(c_1322,plain,(
    r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1321])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_56,plain,(
    ! [A_79,B_81] :
      ( k16_lattice3(A_79,a_2_2_lattice3(A_79,B_81)) = k15_lattice3(A_79,B_81)
      | ~ l3_lattices(A_79)
      | ~ v4_lattice3(A_79)
      | ~ v10_lattices(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_560,plain,(
    ! [A_208,D_209,C_210] :
      ( r3_lattices(A_208,D_209,k16_lattice3(A_208,C_210))
      | ~ r3_lattice3(A_208,D_209,C_210)
      | ~ m1_subset_1(D_209,u1_struct_0(A_208))
      | ~ m1_subset_1(k16_lattice3(A_208,C_210),u1_struct_0(A_208))
      | ~ l3_lattices(A_208)
      | ~ v4_lattice3(A_208)
      | ~ v10_lattices(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_574,plain,(
    ! [A_212,D_213,B_214] :
      ( r3_lattices(A_212,D_213,k16_lattice3(A_212,B_214))
      | ~ r3_lattice3(A_212,D_213,B_214)
      | ~ m1_subset_1(D_213,u1_struct_0(A_212))
      | ~ v4_lattice3(A_212)
      | ~ v10_lattices(A_212)
      | ~ l3_lattices(A_212)
      | v2_struct_0(A_212) ) ),
    inference(resolution,[status(thm)],[c_36,c_560])).

tff(c_925,plain,(
    ! [A_260,D_261,B_262] :
      ( r3_lattices(A_260,D_261,k15_lattice3(A_260,B_262))
      | ~ r3_lattice3(A_260,D_261,a_2_2_lattice3(A_260,B_262))
      | ~ m1_subset_1(D_261,u1_struct_0(A_260))
      | ~ v4_lattice3(A_260)
      | ~ v10_lattices(A_260)
      | ~ l3_lattices(A_260)
      | v2_struct_0(A_260)
      | ~ l3_lattices(A_260)
      | ~ v4_lattice3(A_260)
      | ~ v10_lattices(A_260)
      | v2_struct_0(A_260) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_574])).

tff(c_58,plain,
    ( ~ r3_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ r3_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_74,plain,(
    ~ r3_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_934,plain,
    ( ~ r3_lattice3('#skF_5','#skF_6',a_2_2_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_925,c_74])).

tff(c_939,plain,
    ( ~ r3_lattice3('#skF_5','#skF_6',a_2_2_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_934])).

tff(c_940,plain,(
    ~ r3_lattice3('#skF_5','#skF_6',a_2_2_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_939])).

tff(c_24,plain,(
    ! [A_5,B_17,C_23] :
      ( r2_hidden('#skF_1'(A_5,B_17,C_23),C_23)
      | r3_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_93,plain,(
    ! [A_102,B_103,C_104] :
      ( '#skF_3'(A_102,B_103,C_104) = A_102
      | ~ r2_hidden(A_102,a_2_2_lattice3(B_103,C_104))
      | ~ l3_lattices(B_103)
      | ~ v4_lattice3(B_103)
      | ~ v10_lattices(B_103)
      | v2_struct_0(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1001,plain,(
    ! [A_281,B_282,B_283,C_284] :
      ( '#skF_3'('#skF_1'(A_281,B_282,a_2_2_lattice3(B_283,C_284)),B_283,C_284) = '#skF_1'(A_281,B_282,a_2_2_lattice3(B_283,C_284))
      | ~ l3_lattices(B_283)
      | ~ v4_lattice3(B_283)
      | ~ v10_lattices(B_283)
      | v2_struct_0(B_283)
      | r3_lattice3(A_281,B_282,a_2_2_lattice3(B_283,C_284))
      | ~ m1_subset_1(B_282,u1_struct_0(A_281))
      | ~ l3_lattices(A_281)
      | v2_struct_0(A_281) ) ),
    inference(resolution,[status(thm)],[c_24,c_93])).

tff(c_40,plain,(
    ! [B_52,A_51,C_53] :
      ( r4_lattice3(B_52,'#skF_3'(A_51,B_52,C_53),C_53)
      | ~ r2_hidden(A_51,a_2_2_lattice3(B_52,C_53))
      | ~ l3_lattices(B_52)
      | ~ v4_lattice3(B_52)
      | ~ v10_lattices(B_52)
      | v2_struct_0(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_44,plain,(
    ! [A_51,B_52,C_53] :
      ( m1_subset_1('#skF_3'(A_51,B_52,C_53),u1_struct_0(B_52))
      | ~ r2_hidden(A_51,a_2_2_lattice3(B_52,C_53))
      | ~ l3_lattices(B_52)
      | ~ v4_lattice3(B_52)
      | ~ v10_lattices(B_52)
      | v2_struct_0(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_193,plain,(
    ! [A_140,D_141,B_142,C_143] :
      ( r1_lattices(A_140,D_141,B_142)
      | ~ r2_hidden(D_141,C_143)
      | ~ m1_subset_1(D_141,u1_struct_0(A_140))
      | ~ r4_lattice3(A_140,B_142,C_143)
      | ~ m1_subset_1(B_142,u1_struct_0(A_140))
      | ~ l3_lattices(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_231,plain,(
    ! [A_148,B_149] :
      ( r1_lattices(A_148,'#skF_6',B_149)
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_148))
      | ~ r4_lattice3(A_148,B_149,'#skF_7')
      | ~ m1_subset_1(B_149,u1_struct_0(A_148))
      | ~ l3_lattices(A_148)
      | v2_struct_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_60,c_193])).

tff(c_233,plain,(
    ! [B_149] :
      ( r1_lattices('#skF_5','#skF_6',B_149)
      | ~ r4_lattice3('#skF_5',B_149,'#skF_7')
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_231])).

tff(c_236,plain,(
    ! [B_149] :
      ( r1_lattices('#skF_5','#skF_6',B_149)
      | ~ r4_lattice3('#skF_5',B_149,'#skF_7')
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_233])).

tff(c_238,plain,(
    ! [B_150] :
      ( r1_lattices('#skF_5','#skF_6',B_150)
      | ~ r4_lattice3('#skF_5',B_150,'#skF_7')
      | ~ m1_subset_1(B_150,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_236])).

tff(c_242,plain,(
    ! [A_51,C_53] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'(A_51,'#skF_5',C_53))
      | ~ r4_lattice3('#skF_5','#skF_3'(A_51,'#skF_5',C_53),'#skF_7')
      | ~ r2_hidden(A_51,a_2_2_lattice3('#skF_5',C_53))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_238])).

tff(c_264,plain,(
    ! [A_51,C_53] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'(A_51,'#skF_5',C_53))
      | ~ r4_lattice3('#skF_5','#skF_3'(A_51,'#skF_5',C_53),'#skF_7')
      | ~ r2_hidden(A_51,a_2_2_lattice3('#skF_5',C_53))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_242])).

tff(c_366,plain,(
    ! [A_162,C_163] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'(A_162,'#skF_5',C_163))
      | ~ r4_lattice3('#skF_5','#skF_3'(A_162,'#skF_5',C_163),'#skF_7')
      | ~ r2_hidden(A_162,a_2_2_lattice3('#skF_5',C_163)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_264])).

tff(c_370,plain,(
    ! [A_51] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'(A_51,'#skF_5','#skF_7'))
      | ~ r2_hidden(A_51,a_2_2_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_366])).

tff(c_373,plain,(
    ! [A_51] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'(A_51,'#skF_5','#skF_7'))
      | ~ r2_hidden(A_51,a_2_2_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_370])).

tff(c_374,plain,(
    ! [A_51] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'(A_51,'#skF_5','#skF_7'))
      | ~ r2_hidden(A_51,a_2_2_lattice3('#skF_5','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_373])).

tff(c_1012,plain,(
    ! [A_281,B_282] :
      ( r1_lattices('#skF_5','#skF_6','#skF_1'(A_281,B_282,a_2_2_lattice3('#skF_5','#skF_7')))
      | ~ r2_hidden('#skF_1'(A_281,B_282,a_2_2_lattice3('#skF_5','#skF_7')),a_2_2_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | r3_lattice3(A_281,B_282,a_2_2_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_282,u1_struct_0(A_281))
      | ~ l3_lattices(A_281)
      | v2_struct_0(A_281) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1001,c_374])).

tff(c_1035,plain,(
    ! [A_281,B_282] :
      ( r1_lattices('#skF_5','#skF_6','#skF_1'(A_281,B_282,a_2_2_lattice3('#skF_5','#skF_7')))
      | ~ r2_hidden('#skF_1'(A_281,B_282,a_2_2_lattice3('#skF_5','#skF_7')),a_2_2_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5')
      | r3_lattice3(A_281,B_282,a_2_2_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_282,u1_struct_0(A_281))
      | ~ l3_lattices(A_281)
      | v2_struct_0(A_281) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_1012])).

tff(c_1049,plain,(
    ! [A_289,B_290] :
      ( r1_lattices('#skF_5','#skF_6','#skF_1'(A_289,B_290,a_2_2_lattice3('#skF_5','#skF_7')))
      | ~ r2_hidden('#skF_1'(A_289,B_290,a_2_2_lattice3('#skF_5','#skF_7')),a_2_2_lattice3('#skF_5','#skF_7'))
      | r3_lattice3(A_289,B_290,a_2_2_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_290,u1_struct_0(A_289))
      | ~ l3_lattices(A_289)
      | v2_struct_0(A_289) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1035])).

tff(c_1077,plain,(
    ! [A_293,B_294] :
      ( r1_lattices('#skF_5','#skF_6','#skF_1'(A_293,B_294,a_2_2_lattice3('#skF_5','#skF_7')))
      | r3_lattice3(A_293,B_294,a_2_2_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_294,u1_struct_0(A_293))
      | ~ l3_lattices(A_293)
      | v2_struct_0(A_293) ) ),
    inference(resolution,[status(thm)],[c_24,c_1049])).

tff(c_22,plain,(
    ! [A_5,B_17,C_23] :
      ( ~ r1_lattices(A_5,B_17,'#skF_1'(A_5,B_17,C_23))
      | r3_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1081,plain,
    ( r3_lattice3('#skF_5','#skF_6',a_2_2_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1077,c_22])).

tff(c_1084,plain,
    ( r3_lattice3('#skF_5','#skF_6',a_2_2_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1081])).

tff(c_1086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_940,c_1084])).

tff(c_1088,plain,(
    r3_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1302,plain,(
    ! [A_361,B_362,C_363] :
      ( r1_lattices(A_361,B_362,C_363)
      | ~ r3_lattices(A_361,B_362,C_363)
      | ~ m1_subset_1(C_363,u1_struct_0(A_361))
      | ~ m1_subset_1(B_362,u1_struct_0(A_361))
      | ~ l3_lattices(A_361)
      | ~ v9_lattices(A_361)
      | ~ v8_lattices(A_361)
      | ~ v6_lattices(A_361)
      | v2_struct_0(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1304,plain,
    ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1088,c_1302])).

tff(c_1307,plain,
    ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1304])).

tff(c_1308,plain,
    ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1307])).

tff(c_1335,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1308])).

tff(c_1338,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_1335])).

tff(c_1341,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_1338])).

tff(c_1343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1341])).

tff(c_1345,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1308])).

tff(c_1346,plain,(
    ! [A_367,B_368,C_369] :
      ( r3_lattices(A_367,B_368,C_369)
      | ~ r1_lattices(A_367,B_368,C_369)
      | ~ m1_subset_1(C_369,u1_struct_0(A_367))
      | ~ m1_subset_1(B_368,u1_struct_0(A_367))
      | ~ l3_lattices(A_367)
      | ~ v9_lattices(A_367)
      | ~ v8_lattices(A_367)
      | ~ v6_lattices(A_367)
      | v2_struct_0(A_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1358,plain,(
    ! [B_368] :
      ( r3_lattices('#skF_5',B_368,'#skF_6')
      | ~ r1_lattices('#skF_5',B_368,'#skF_6')
      | ~ m1_subset_1(B_368,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_1346])).

tff(c_1366,plain,(
    ! [B_368] :
      ( r3_lattices('#skF_5',B_368,'#skF_6')
      | ~ r1_lattices('#skF_5',B_368,'#skF_6')
      | ~ m1_subset_1(B_368,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1345,c_64,c_1358])).

tff(c_1367,plain,(
    ! [B_368] :
      ( r3_lattices('#skF_5',B_368,'#skF_6')
      | ~ r1_lattices('#skF_5',B_368,'#skF_6')
      | ~ m1_subset_1(B_368,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1366])).

tff(c_1393,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1367])).

tff(c_1396,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_1393])).

tff(c_1399,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_1396])).

tff(c_1401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1399])).

tff(c_1403,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1367])).

tff(c_1093,plain,(
    ! [A_300,B_301] :
      ( k16_lattice3(A_300,a_2_2_lattice3(A_300,B_301)) = k15_lattice3(A_300,B_301)
      | ~ l3_lattices(A_300)
      | ~ v4_lattice3(A_300)
      | ~ v10_lattices(A_300)
      | v2_struct_0(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1099,plain,(
    ! [A_300,B_301] :
      ( m1_subset_1(k15_lattice3(A_300,B_301),u1_struct_0(A_300))
      | ~ l3_lattices(A_300)
      | v2_struct_0(A_300)
      | ~ l3_lattices(A_300)
      | ~ v4_lattice3(A_300)
      | ~ v10_lattices(A_300)
      | v2_struct_0(A_300) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_36])).

tff(c_1344,plain,
    ( ~ v8_lattices('#skF_5')
    | ~ v9_lattices('#skF_5')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1308])).

tff(c_1368,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1344])).

tff(c_1371,plain,
    ( ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1099,c_1368])).

tff(c_1374,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_1371])).

tff(c_1376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1374])).

tff(c_1377,plain,
    ( ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1344])).

tff(c_1405,plain,
    ( ~ v9_lattices('#skF_5')
    | r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_1377])).

tff(c_1406,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1405])).

tff(c_1409,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_1406])).

tff(c_1412,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_1409])).

tff(c_1414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1412])).

tff(c_1416,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1405])).

tff(c_1402,plain,(
    ! [B_368] :
      ( ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_368,'#skF_6')
      | ~ r1_lattices('#skF_5',B_368,'#skF_6')
      | ~ m1_subset_1(B_368,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_1367])).

tff(c_1420,plain,(
    ! [B_373] :
      ( r3_lattices('#skF_5',B_373,'#skF_6')
      | ~ r1_lattices('#skF_5',B_373,'#skF_6')
      | ~ m1_subset_1(B_373,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1416,c_1402])).

tff(c_1443,plain,(
    ! [B_50] :
      ( r3_lattices('#skF_5',k16_lattice3('#skF_5',B_50),'#skF_6')
      | ~ r1_lattices('#skF_5',k16_lattice3('#skF_5',B_50),'#skF_6')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_1420])).

tff(c_1466,plain,(
    ! [B_50] :
      ( r3_lattices('#skF_5',k16_lattice3('#skF_5',B_50),'#skF_6')
      | ~ r1_lattices('#skF_5',k16_lattice3('#skF_5',B_50),'#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1443])).

tff(c_1477,plain,(
    ! [B_375] :
      ( r3_lattices('#skF_5',k16_lattice3('#skF_5',B_375),'#skF_6')
      | ~ r1_lattices('#skF_5',k16_lattice3('#skF_5',B_375),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1466])).

tff(c_1087,plain,(
    ~ r3_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1482,plain,(
    ~ r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1477,c_1087])).

tff(c_1494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1322,c_1482])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:28:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.12/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.74  
% 4.12/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.75  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 4.12/1.75  
% 4.12/1.75  %Foreground sorts:
% 4.12/1.75  
% 4.12/1.75  
% 4.12/1.75  %Background operators:
% 4.12/1.75  
% 4.12/1.75  
% 4.12/1.75  %Foreground operators:
% 4.12/1.75  tff(l3_lattices, type, l3_lattices: $i > $o).
% 4.12/1.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.12/1.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.12/1.75  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 4.12/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.12/1.75  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 4.12/1.75  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 4.12/1.75  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.12/1.75  tff('#skF_7', type, '#skF_7': $i).
% 4.12/1.75  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 4.12/1.75  tff('#skF_5', type, '#skF_5': $i).
% 4.12/1.75  tff(v4_lattices, type, v4_lattices: $i > $o).
% 4.12/1.75  tff('#skF_6', type, '#skF_6': $i).
% 4.12/1.75  tff(v6_lattices, type, v6_lattices: $i > $o).
% 4.12/1.75  tff(v9_lattices, type, v9_lattices: $i > $o).
% 4.12/1.75  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 4.12/1.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.12/1.75  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 4.12/1.75  tff(v5_lattices, type, v5_lattices: $i > $o).
% 4.12/1.75  tff(v10_lattices, type, v10_lattices: $i > $o).
% 4.12/1.75  tff(a_2_2_lattice3, type, a_2_2_lattice3: ($i * $i) > $i).
% 4.12/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/1.75  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.12/1.75  tff(v8_lattices, type, v8_lattices: $i > $o).
% 4.12/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/1.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.12/1.75  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 4.12/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.12/1.75  tff(v7_lattices, type, v7_lattices: $i > $o).
% 4.12/1.75  
% 4.12/1.77  tff(f_183, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 4.12/1.77  tff(f_109, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k16_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 4.12/1.77  tff(f_151, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 4.12/1.77  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 4.12/1.77  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 4.12/1.77  tff(f_163, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (k15_lattice3(A, B) = k16_lattice3(A, a_2_2_lattice3(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 4.12/1.77  tff(f_127, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_2_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r4_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 4.12/1.77  tff(f_102, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 4.12/1.77  tff(f_66, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 4.12/1.77  tff(c_70, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.12/1.77  tff(c_64, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.12/1.77  tff(c_68, plain, (v10_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.12/1.77  tff(c_66, plain, (v4_lattice3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.12/1.77  tff(c_36, plain, (![A_49, B_50]: (m1_subset_1(k16_lattice3(A_49, B_50), u1_struct_0(A_49)) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.12/1.77  tff(c_1123, plain, (![A_325, C_326]: (r3_lattice3(A_325, k16_lattice3(A_325, C_326), C_326) | ~m1_subset_1(k16_lattice3(A_325, C_326), u1_struct_0(A_325)) | ~l3_lattices(A_325) | ~v4_lattice3(A_325) | ~v10_lattices(A_325) | v2_struct_0(A_325))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.12/1.77  tff(c_1128, plain, (![A_49, B_50]: (r3_lattice3(A_49, k16_lattice3(A_49, B_50), B_50) | ~v4_lattice3(A_49) | ~v10_lattices(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(resolution, [status(thm)], [c_36, c_1123])).
% 4.12/1.77  tff(c_62, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.12/1.77  tff(c_60, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.12/1.77  tff(c_1209, plain, (![A_348, B_349, D_350, C_351]: (r1_lattices(A_348, B_349, D_350) | ~r2_hidden(D_350, C_351) | ~m1_subset_1(D_350, u1_struct_0(A_348)) | ~r3_lattice3(A_348, B_349, C_351) | ~m1_subset_1(B_349, u1_struct_0(A_348)) | ~l3_lattices(A_348) | v2_struct_0(A_348))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.12/1.77  tff(c_1250, plain, (![A_358, B_359]: (r1_lattices(A_358, B_359, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0(A_358)) | ~r3_lattice3(A_358, B_359, '#skF_7') | ~m1_subset_1(B_359, u1_struct_0(A_358)) | ~l3_lattices(A_358) | v2_struct_0(A_358))), inference(resolution, [status(thm)], [c_60, c_1209])).
% 4.12/1.77  tff(c_1252, plain, (![B_359]: (r1_lattices('#skF_5', B_359, '#skF_6') | ~r3_lattice3('#skF_5', B_359, '#skF_7') | ~m1_subset_1(B_359, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_62, c_1250])).
% 4.12/1.77  tff(c_1255, plain, (![B_359]: (r1_lattices('#skF_5', B_359, '#skF_6') | ~r3_lattice3('#skF_5', B_359, '#skF_7') | ~m1_subset_1(B_359, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1252])).
% 4.12/1.77  tff(c_1257, plain, (![B_360]: (r1_lattices('#skF_5', B_360, '#skF_6') | ~r3_lattice3('#skF_5', B_360, '#skF_7') | ~m1_subset_1(B_360, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_70, c_1255])).
% 4.12/1.77  tff(c_1277, plain, (![B_50]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', B_50), '#skF_6') | ~r3_lattice3('#skF_5', k16_lattice3('#skF_5', B_50), '#skF_7') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_1257])).
% 4.12/1.77  tff(c_1299, plain, (![B_50]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', B_50), '#skF_6') | ~r3_lattice3('#skF_5', k16_lattice3('#skF_5', B_50), '#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1277])).
% 4.12/1.77  tff(c_1310, plain, (![B_364]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', B_364), '#skF_6') | ~r3_lattice3('#skF_5', k16_lattice3('#skF_5', B_364), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1299])).
% 4.12/1.77  tff(c_1314, plain, (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1128, c_1310])).
% 4.12/1.77  tff(c_1321, plain, (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_66, c_1314])).
% 4.12/1.77  tff(c_1322, plain, (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_70, c_1321])).
% 4.12/1.77  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.12/1.77  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.12/1.77  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.12/1.77  tff(c_56, plain, (![A_79, B_81]: (k16_lattice3(A_79, a_2_2_lattice3(A_79, B_81))=k15_lattice3(A_79, B_81) | ~l3_lattices(A_79) | ~v4_lattice3(A_79) | ~v10_lattices(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.12/1.77  tff(c_560, plain, (![A_208, D_209, C_210]: (r3_lattices(A_208, D_209, k16_lattice3(A_208, C_210)) | ~r3_lattice3(A_208, D_209, C_210) | ~m1_subset_1(D_209, u1_struct_0(A_208)) | ~m1_subset_1(k16_lattice3(A_208, C_210), u1_struct_0(A_208)) | ~l3_lattices(A_208) | ~v4_lattice3(A_208) | ~v10_lattices(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.12/1.77  tff(c_574, plain, (![A_212, D_213, B_214]: (r3_lattices(A_212, D_213, k16_lattice3(A_212, B_214)) | ~r3_lattice3(A_212, D_213, B_214) | ~m1_subset_1(D_213, u1_struct_0(A_212)) | ~v4_lattice3(A_212) | ~v10_lattices(A_212) | ~l3_lattices(A_212) | v2_struct_0(A_212))), inference(resolution, [status(thm)], [c_36, c_560])).
% 4.12/1.77  tff(c_925, plain, (![A_260, D_261, B_262]: (r3_lattices(A_260, D_261, k15_lattice3(A_260, B_262)) | ~r3_lattice3(A_260, D_261, a_2_2_lattice3(A_260, B_262)) | ~m1_subset_1(D_261, u1_struct_0(A_260)) | ~v4_lattice3(A_260) | ~v10_lattices(A_260) | ~l3_lattices(A_260) | v2_struct_0(A_260) | ~l3_lattices(A_260) | ~v4_lattice3(A_260) | ~v10_lattices(A_260) | v2_struct_0(A_260))), inference(superposition, [status(thm), theory('equality')], [c_56, c_574])).
% 4.12/1.77  tff(c_58, plain, (~r3_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~r3_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.12/1.77  tff(c_74, plain, (~r3_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_58])).
% 4.12/1.77  tff(c_934, plain, (~r3_lattice3('#skF_5', '#skF_6', a_2_2_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_925, c_74])).
% 4.12/1.77  tff(c_939, plain, (~r3_lattice3('#skF_5', '#skF_6', a_2_2_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_934])).
% 4.12/1.77  tff(c_940, plain, (~r3_lattice3('#skF_5', '#skF_6', a_2_2_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_70, c_939])).
% 4.12/1.77  tff(c_24, plain, (![A_5, B_17, C_23]: (r2_hidden('#skF_1'(A_5, B_17, C_23), C_23) | r3_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.12/1.77  tff(c_93, plain, (![A_102, B_103, C_104]: ('#skF_3'(A_102, B_103, C_104)=A_102 | ~r2_hidden(A_102, a_2_2_lattice3(B_103, C_104)) | ~l3_lattices(B_103) | ~v4_lattice3(B_103) | ~v10_lattices(B_103) | v2_struct_0(B_103))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.12/1.77  tff(c_1001, plain, (![A_281, B_282, B_283, C_284]: ('#skF_3'('#skF_1'(A_281, B_282, a_2_2_lattice3(B_283, C_284)), B_283, C_284)='#skF_1'(A_281, B_282, a_2_2_lattice3(B_283, C_284)) | ~l3_lattices(B_283) | ~v4_lattice3(B_283) | ~v10_lattices(B_283) | v2_struct_0(B_283) | r3_lattice3(A_281, B_282, a_2_2_lattice3(B_283, C_284)) | ~m1_subset_1(B_282, u1_struct_0(A_281)) | ~l3_lattices(A_281) | v2_struct_0(A_281))), inference(resolution, [status(thm)], [c_24, c_93])).
% 4.12/1.77  tff(c_40, plain, (![B_52, A_51, C_53]: (r4_lattice3(B_52, '#skF_3'(A_51, B_52, C_53), C_53) | ~r2_hidden(A_51, a_2_2_lattice3(B_52, C_53)) | ~l3_lattices(B_52) | ~v4_lattice3(B_52) | ~v10_lattices(B_52) | v2_struct_0(B_52))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.12/1.77  tff(c_44, plain, (![A_51, B_52, C_53]: (m1_subset_1('#skF_3'(A_51, B_52, C_53), u1_struct_0(B_52)) | ~r2_hidden(A_51, a_2_2_lattice3(B_52, C_53)) | ~l3_lattices(B_52) | ~v4_lattice3(B_52) | ~v10_lattices(B_52) | v2_struct_0(B_52))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.12/1.77  tff(c_193, plain, (![A_140, D_141, B_142, C_143]: (r1_lattices(A_140, D_141, B_142) | ~r2_hidden(D_141, C_143) | ~m1_subset_1(D_141, u1_struct_0(A_140)) | ~r4_lattice3(A_140, B_142, C_143) | ~m1_subset_1(B_142, u1_struct_0(A_140)) | ~l3_lattices(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.12/1.77  tff(c_231, plain, (![A_148, B_149]: (r1_lattices(A_148, '#skF_6', B_149) | ~m1_subset_1('#skF_6', u1_struct_0(A_148)) | ~r4_lattice3(A_148, B_149, '#skF_7') | ~m1_subset_1(B_149, u1_struct_0(A_148)) | ~l3_lattices(A_148) | v2_struct_0(A_148))), inference(resolution, [status(thm)], [c_60, c_193])).
% 4.12/1.77  tff(c_233, plain, (![B_149]: (r1_lattices('#skF_5', '#skF_6', B_149) | ~r4_lattice3('#skF_5', B_149, '#skF_7') | ~m1_subset_1(B_149, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_62, c_231])).
% 4.12/1.77  tff(c_236, plain, (![B_149]: (r1_lattices('#skF_5', '#skF_6', B_149) | ~r4_lattice3('#skF_5', B_149, '#skF_7') | ~m1_subset_1(B_149, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_233])).
% 4.12/1.77  tff(c_238, plain, (![B_150]: (r1_lattices('#skF_5', '#skF_6', B_150) | ~r4_lattice3('#skF_5', B_150, '#skF_7') | ~m1_subset_1(B_150, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_70, c_236])).
% 4.12/1.77  tff(c_242, plain, (![A_51, C_53]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'(A_51, '#skF_5', C_53)) | ~r4_lattice3('#skF_5', '#skF_3'(A_51, '#skF_5', C_53), '#skF_7') | ~r2_hidden(A_51, a_2_2_lattice3('#skF_5', C_53)) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_238])).
% 4.12/1.77  tff(c_264, plain, (![A_51, C_53]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'(A_51, '#skF_5', C_53)) | ~r4_lattice3('#skF_5', '#skF_3'(A_51, '#skF_5', C_53), '#skF_7') | ~r2_hidden(A_51, a_2_2_lattice3('#skF_5', C_53)) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_242])).
% 4.12/1.77  tff(c_366, plain, (![A_162, C_163]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'(A_162, '#skF_5', C_163)) | ~r4_lattice3('#skF_5', '#skF_3'(A_162, '#skF_5', C_163), '#skF_7') | ~r2_hidden(A_162, a_2_2_lattice3('#skF_5', C_163)))), inference(negUnitSimplification, [status(thm)], [c_70, c_264])).
% 4.12/1.77  tff(c_370, plain, (![A_51]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'(A_51, '#skF_5', '#skF_7')) | ~r2_hidden(A_51, a_2_2_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_366])).
% 4.12/1.77  tff(c_373, plain, (![A_51]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'(A_51, '#skF_5', '#skF_7')) | ~r2_hidden(A_51, a_2_2_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_370])).
% 4.12/1.77  tff(c_374, plain, (![A_51]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'(A_51, '#skF_5', '#skF_7')) | ~r2_hidden(A_51, a_2_2_lattice3('#skF_5', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_70, c_373])).
% 4.12/1.77  tff(c_1012, plain, (![A_281, B_282]: (r1_lattices('#skF_5', '#skF_6', '#skF_1'(A_281, B_282, a_2_2_lattice3('#skF_5', '#skF_7'))) | ~r2_hidden('#skF_1'(A_281, B_282, a_2_2_lattice3('#skF_5', '#skF_7')), a_2_2_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | r3_lattice3(A_281, B_282, a_2_2_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_282, u1_struct_0(A_281)) | ~l3_lattices(A_281) | v2_struct_0(A_281))), inference(superposition, [status(thm), theory('equality')], [c_1001, c_374])).
% 4.12/1.77  tff(c_1035, plain, (![A_281, B_282]: (r1_lattices('#skF_5', '#skF_6', '#skF_1'(A_281, B_282, a_2_2_lattice3('#skF_5', '#skF_7'))) | ~r2_hidden('#skF_1'(A_281, B_282, a_2_2_lattice3('#skF_5', '#skF_7')), a_2_2_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5') | r3_lattice3(A_281, B_282, a_2_2_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_282, u1_struct_0(A_281)) | ~l3_lattices(A_281) | v2_struct_0(A_281))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_1012])).
% 4.12/1.77  tff(c_1049, plain, (![A_289, B_290]: (r1_lattices('#skF_5', '#skF_6', '#skF_1'(A_289, B_290, a_2_2_lattice3('#skF_5', '#skF_7'))) | ~r2_hidden('#skF_1'(A_289, B_290, a_2_2_lattice3('#skF_5', '#skF_7')), a_2_2_lattice3('#skF_5', '#skF_7')) | r3_lattice3(A_289, B_290, a_2_2_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_290, u1_struct_0(A_289)) | ~l3_lattices(A_289) | v2_struct_0(A_289))), inference(negUnitSimplification, [status(thm)], [c_70, c_1035])).
% 4.12/1.77  tff(c_1077, plain, (![A_293, B_294]: (r1_lattices('#skF_5', '#skF_6', '#skF_1'(A_293, B_294, a_2_2_lattice3('#skF_5', '#skF_7'))) | r3_lattice3(A_293, B_294, a_2_2_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_294, u1_struct_0(A_293)) | ~l3_lattices(A_293) | v2_struct_0(A_293))), inference(resolution, [status(thm)], [c_24, c_1049])).
% 4.12/1.77  tff(c_22, plain, (![A_5, B_17, C_23]: (~r1_lattices(A_5, B_17, '#skF_1'(A_5, B_17, C_23)) | r3_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.12/1.77  tff(c_1081, plain, (r3_lattice3('#skF_5', '#skF_6', a_2_2_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1077, c_22])).
% 4.12/1.77  tff(c_1084, plain, (r3_lattice3('#skF_5', '#skF_6', a_2_2_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1081])).
% 4.12/1.77  tff(c_1086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_940, c_1084])).
% 4.12/1.77  tff(c_1088, plain, (r3_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_58])).
% 4.12/1.77  tff(c_1302, plain, (![A_361, B_362, C_363]: (r1_lattices(A_361, B_362, C_363) | ~r3_lattices(A_361, B_362, C_363) | ~m1_subset_1(C_363, u1_struct_0(A_361)) | ~m1_subset_1(B_362, u1_struct_0(A_361)) | ~l3_lattices(A_361) | ~v9_lattices(A_361) | ~v8_lattices(A_361) | ~v6_lattices(A_361) | v2_struct_0(A_361))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.12/1.77  tff(c_1304, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1088, c_1302])).
% 4.12/1.77  tff(c_1307, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1304])).
% 4.12/1.77  tff(c_1308, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_1307])).
% 4.12/1.77  tff(c_1335, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_1308])).
% 4.12/1.77  tff(c_1338, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_1335])).
% 4.12/1.77  tff(c_1341, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_1338])).
% 4.12/1.77  tff(c_1343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1341])).
% 4.12/1.77  tff(c_1345, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_1308])).
% 4.12/1.77  tff(c_1346, plain, (![A_367, B_368, C_369]: (r3_lattices(A_367, B_368, C_369) | ~r1_lattices(A_367, B_368, C_369) | ~m1_subset_1(C_369, u1_struct_0(A_367)) | ~m1_subset_1(B_368, u1_struct_0(A_367)) | ~l3_lattices(A_367) | ~v9_lattices(A_367) | ~v8_lattices(A_367) | ~v6_lattices(A_367) | v2_struct_0(A_367))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.12/1.77  tff(c_1358, plain, (![B_368]: (r3_lattices('#skF_5', B_368, '#skF_6') | ~r1_lattices('#skF_5', B_368, '#skF_6') | ~m1_subset_1(B_368, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_62, c_1346])).
% 4.12/1.77  tff(c_1366, plain, (![B_368]: (r3_lattices('#skF_5', B_368, '#skF_6') | ~r1_lattices('#skF_5', B_368, '#skF_6') | ~m1_subset_1(B_368, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1345, c_64, c_1358])).
% 4.12/1.77  tff(c_1367, plain, (![B_368]: (r3_lattices('#skF_5', B_368, '#skF_6') | ~r1_lattices('#skF_5', B_368, '#skF_6') | ~m1_subset_1(B_368, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1366])).
% 4.12/1.77  tff(c_1393, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_1367])).
% 4.12/1.77  tff(c_1396, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_1393])).
% 4.12/1.77  tff(c_1399, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_1396])).
% 4.12/1.77  tff(c_1401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1399])).
% 4.12/1.77  tff(c_1403, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_1367])).
% 4.12/1.77  tff(c_1093, plain, (![A_300, B_301]: (k16_lattice3(A_300, a_2_2_lattice3(A_300, B_301))=k15_lattice3(A_300, B_301) | ~l3_lattices(A_300) | ~v4_lattice3(A_300) | ~v10_lattices(A_300) | v2_struct_0(A_300))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.12/1.77  tff(c_1099, plain, (![A_300, B_301]: (m1_subset_1(k15_lattice3(A_300, B_301), u1_struct_0(A_300)) | ~l3_lattices(A_300) | v2_struct_0(A_300) | ~l3_lattices(A_300) | ~v4_lattice3(A_300) | ~v10_lattices(A_300) | v2_struct_0(A_300))), inference(superposition, [status(thm), theory('equality')], [c_1093, c_36])).
% 4.12/1.77  tff(c_1344, plain, (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_1308])).
% 4.12/1.77  tff(c_1368, plain, (~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_1344])).
% 4.12/1.77  tff(c_1371, plain, (~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1099, c_1368])).
% 4.12/1.77  tff(c_1374, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_1371])).
% 4.12/1.77  tff(c_1376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1374])).
% 4.12/1.77  tff(c_1377, plain, (~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_1344])).
% 4.12/1.77  tff(c_1405, plain, (~v9_lattices('#skF_5') | r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_1377])).
% 4.12/1.77  tff(c_1406, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_1405])).
% 4.12/1.77  tff(c_1409, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_1406])).
% 4.12/1.77  tff(c_1412, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_1409])).
% 4.12/1.77  tff(c_1414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1412])).
% 4.12/1.77  tff(c_1416, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_1405])).
% 4.12/1.77  tff(c_1402, plain, (![B_368]: (~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_368, '#skF_6') | ~r1_lattices('#skF_5', B_368, '#skF_6') | ~m1_subset_1(B_368, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_1367])).
% 4.12/1.77  tff(c_1420, plain, (![B_373]: (r3_lattices('#skF_5', B_373, '#skF_6') | ~r1_lattices('#skF_5', B_373, '#skF_6') | ~m1_subset_1(B_373, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1416, c_1402])).
% 4.12/1.77  tff(c_1443, plain, (![B_50]: (r3_lattices('#skF_5', k16_lattice3('#skF_5', B_50), '#skF_6') | ~r1_lattices('#skF_5', k16_lattice3('#skF_5', B_50), '#skF_6') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_1420])).
% 4.12/1.77  tff(c_1466, plain, (![B_50]: (r3_lattices('#skF_5', k16_lattice3('#skF_5', B_50), '#skF_6') | ~r1_lattices('#skF_5', k16_lattice3('#skF_5', B_50), '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1443])).
% 4.12/1.77  tff(c_1477, plain, (![B_375]: (r3_lattices('#skF_5', k16_lattice3('#skF_5', B_375), '#skF_6') | ~r1_lattices('#skF_5', k16_lattice3('#skF_5', B_375), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1466])).
% 4.12/1.77  tff(c_1087, plain, (~r3_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 4.12/1.77  tff(c_1482, plain, (~r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_1477, c_1087])).
% 4.12/1.77  tff(c_1494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1322, c_1482])).
% 4.12/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.77  
% 4.12/1.77  Inference rules
% 4.12/1.77  ----------------------
% 4.12/1.77  #Ref     : 0
% 4.12/1.77  #Sup     : 233
% 4.12/1.77  #Fact    : 0
% 4.12/1.77  #Define  : 0
% 4.12/1.77  #Split   : 14
% 4.12/1.77  #Chain   : 0
% 4.12/1.77  #Close   : 0
% 4.12/1.77  
% 4.12/1.77  Ordering : KBO
% 4.12/1.77  
% 4.12/1.77  Simplification rules
% 4.12/1.77  ----------------------
% 4.12/1.77  #Subsume      : 30
% 4.12/1.77  #Demod        : 314
% 4.12/1.77  #Tautology    : 27
% 4.12/1.77  #SimpNegUnit  : 112
% 4.12/1.77  #BackRed      : 0
% 4.12/1.77  
% 4.12/1.77  #Partial instantiations: 0
% 4.12/1.77  #Strategies tried      : 1
% 4.12/1.77  
% 4.12/1.77  Timing (in seconds)
% 4.12/1.77  ----------------------
% 4.12/1.77  Preprocessing        : 0.34
% 4.12/1.77  Parsing              : 0.19
% 4.12/1.77  CNF conversion       : 0.03
% 4.12/1.77  Main loop            : 0.61
% 4.12/1.77  Inferencing          : 0.27
% 4.12/1.77  Reduction            : 0.16
% 4.12/1.77  Demodulation         : 0.10
% 4.12/1.77  BG Simplification    : 0.03
% 4.12/1.77  Subsumption          : 0.11
% 4.12/1.77  Abstraction          : 0.03
% 4.12/1.77  MUC search           : 0.00
% 4.12/1.77  Cooper               : 0.00
% 4.12/1.77  Total                : 1.00
% 4.12/1.77  Index Insertion      : 0.00
% 4.12/1.77  Index Deletion       : 0.00
% 4.12/1.77  Index Matching       : 0.00
% 4.12/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
