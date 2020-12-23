%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1995+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:46 EST 2020

% Result     : Theorem 39.39s
% Output     : CNFRefutation 39.57s
% Verified   : 
% Statistics : Number of formulae       :  257 (6280 expanded)
%              Number of leaves         :   44 (2046 expanded)
%              Depth                    :   34
%              Number of atoms          : 1039 (36302 expanded)
%              Number of equality atoms :   54 ( 969 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_waybel_7 > v5_waybel_4 > v2_waybel_0 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_yellow_0 > v1_lattice3 > l1_orders_2 > k7_yellow_3 > k6_waybel_4 > k12_lattice3 > k11_lattice3 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k7_yellow_3,type,(
    k7_yellow_3: ( $i * $i * $i * $i ) > $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(v5_waybel_7,type,(
    v5_waybel_7: ( $i * $i ) > $o )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff(k6_waybel_4,type,(
    k6_waybel_4: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v5_waybel_4,type,(
    v5_waybel_4: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_201,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( v5_waybel_4(B,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) )
           => ( v5_waybel_7(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => v2_waybel_0(k6_waybel_4(A,C,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_waybel_7)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A))))
         => ( v5_waybel_7(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ( ( r2_hidden(k7_yellow_3(A,A,C,D),B)
                            & r2_hidden(k7_yellow_3(A,A,C,E),B) )
                         => r2_hidden(k7_yellow_3(A,A,C,k11_lattice3(A,D,E)),B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_7)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & v5_waybel_4(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A))))
        & m1_subset_1(C,u1_struct_0(A)) )
     => v13_waybel_0(k6_waybel_4(A,C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_waybel_7)).

tff(f_123,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & ~ v2_struct_0(B)
        & l1_orders_2(B)
        & m1_subset_1(C,u1_struct_0(A))
        & m1_subset_1(D,u1_struct_0(B)) )
     => k7_yellow_3(A,B,C,D) = k4_tarski(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_yellow_3)).

tff(f_143,axiom,(
    ! [A,B] :
      ( ( v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & v1_lattice3(B)
        & l1_orders_2(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(B))))
         => ! [D] :
              ( m1_subset_1(D,u1_struct_0(B))
             => ( r2_hidden(A,k6_waybel_4(B,D,C))
              <=> r2_hidden(k4_tarski(D,A),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_waybel_4)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) )
     => m1_subset_1(k6_waybel_4(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_waybel_4)).

tff(f_168,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r2_hidden(D,B) )
                     => r2_hidden(k12_lattice3(A,C,D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_waybel_0)).

tff(f_174,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(c_50,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_52,plain,(
    v2_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_66,plain,
    ( m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ v5_waybel_7('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_76,plain,(
    ~ v5_waybel_7('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_85,plain,(
    ! [A_127,B_128] :
      ( m1_subset_1('#skF_1'(A_127,B_128),u1_struct_0(A_127))
      | v5_waybel_7(B_128,A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_127),u1_struct_0(A_127))))
      | ~ l1_orders_2(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_88,plain,
    ( m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | v5_waybel_7('#skF_7','#skF_6')
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_85])).

tff(c_91,plain,
    ( m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | v5_waybel_7('#skF_7','#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_88])).

tff(c_92,plain,
    ( m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_91])).

tff(c_93,plain,(
    v2_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v2_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,
    ( ~ v2_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_93,c_2])).

tff(c_100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_96])).

tff(c_101,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_62,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_60,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_58,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_56,plain,(
    v1_yellow_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_54,plain,(
    v1_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_48,plain,(
    v5_waybel_4('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_635,plain,(
    ! [A_210,C_211,B_212] :
      ( v13_waybel_0(k6_waybel_4(A_210,C_211,B_212),A_210)
      | ~ m1_subset_1(C_211,u1_struct_0(A_210))
      | ~ m1_subset_1(B_212,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_210),u1_struct_0(A_210))))
      | ~ v5_waybel_4(B_212,A_210)
      | ~ l1_orders_2(A_210)
      | ~ v1_lattice3(A_210)
      | ~ v1_yellow_0(A_210)
      | ~ v5_orders_2(A_210)
      | ~ v4_orders_2(A_210)
      | ~ v3_orders_2(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_637,plain,(
    ! [C_211] :
      ( v13_waybel_0(k6_waybel_4('#skF_6',C_211,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(C_211,u1_struct_0('#skF_6'))
      | ~ v5_waybel_4('#skF_7','#skF_6')
      | ~ l1_orders_2('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v1_yellow_0('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_635])).

tff(c_640,plain,(
    ! [C_211] :
      ( v13_waybel_0(k6_waybel_4('#skF_6',C_211,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(C_211,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_50,c_48,c_637])).

tff(c_102,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_103,plain,(
    ! [A_129,B_130] :
      ( m1_subset_1('#skF_3'(A_129,B_130),u1_struct_0(A_129))
      | v5_waybel_7(B_130,A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_129),u1_struct_0(A_129))))
      | ~ l1_orders_2(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_106,plain,
    ( m1_subset_1('#skF_3'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | v5_waybel_7('#skF_7','#skF_6')
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_103])).

tff(c_109,plain,
    ( m1_subset_1('#skF_3'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | v5_waybel_7('#skF_7','#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_106])).

tff(c_110,plain,(
    m1_subset_1('#skF_3'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_76,c_109])).

tff(c_308,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( k7_yellow_3(A_153,B_154,C_155,D_156) = k4_tarski(C_155,D_156)
      | ~ m1_subset_1(D_156,u1_struct_0(B_154))
      | ~ m1_subset_1(C_155,u1_struct_0(A_153))
      | ~ l1_orders_2(B_154)
      | v2_struct_0(B_154)
      | ~ l1_orders_2(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_316,plain,(
    ! [A_153,C_155] :
      ( k7_yellow_3(A_153,'#skF_6',C_155,'#skF_3'('#skF_6','#skF_7')) = k4_tarski(C_155,'#skF_3'('#skF_6','#skF_7'))
      | ~ m1_subset_1(C_155,u1_struct_0(A_153))
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_orders_2(A_153)
      | v2_struct_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_110,c_308])).

tff(c_329,plain,(
    ! [A_153,C_155] :
      ( k7_yellow_3(A_153,'#skF_6',C_155,'#skF_3'('#skF_6','#skF_7')) = k4_tarski(C_155,'#skF_3'('#skF_6','#skF_7'))
      | ~ m1_subset_1(C_155,u1_struct_0(A_153))
      | v2_struct_0('#skF_6')
      | ~ l1_orders_2(A_153)
      | v2_struct_0(A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_316])).

tff(c_435,plain,(
    ! [A_163,C_164] :
      ( k7_yellow_3(A_163,'#skF_6',C_164,'#skF_3'('#skF_6','#skF_7')) = k4_tarski(C_164,'#skF_3'('#skF_6','#skF_7'))
      | ~ m1_subset_1(C_164,u1_struct_0(A_163))
      | ~ l1_orders_2(A_163)
      | v2_struct_0(A_163) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_329])).

tff(c_450,plain,
    ( k7_yellow_3('#skF_6','#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7')) = k4_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_101,c_435])).

tff(c_466,plain,
    ( k7_yellow_3('#skF_6','#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7')) = k4_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_450])).

tff(c_467,plain,(
    k7_yellow_3('#skF_6','#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7')) = k4_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_466])).

tff(c_420,plain,(
    ! [A_161,B_162] :
      ( r2_hidden(k7_yellow_3(A_161,A_161,'#skF_1'(A_161,B_162),'#skF_3'(A_161,B_162)),B_162)
      | v5_waybel_7(B_162,A_161)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_161),u1_struct_0(A_161))))
      | ~ l1_orders_2(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_422,plain,
    ( r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7')),'#skF_7')
    | v5_waybel_7('#skF_7','#skF_6')
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_420])).

tff(c_425,plain,
    ( r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7')),'#skF_7')
    | v5_waybel_7('#skF_7','#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_422])).

tff(c_426,plain,(
    r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_76,c_425])).

tff(c_477,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_426])).

tff(c_628,plain,(
    ! [A_206,B_207,D_208,C_209] :
      ( r2_hidden(A_206,k6_waybel_4(B_207,D_208,C_209))
      | ~ r2_hidden(k4_tarski(D_208,A_206),C_209)
      | ~ m1_subset_1(D_208,u1_struct_0(B_207))
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_207),u1_struct_0(B_207))))
      | ~ l1_orders_2(B_207)
      | ~ v1_lattice3(B_207)
      | ~ v5_orders_2(B_207)
      | ~ v4_orders_2(B_207)
      | ~ v3_orders_2(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_746,plain,(
    ! [B_231] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_7'),k6_waybel_4(B_231,'#skF_1'('#skF_6','#skF_7'),'#skF_7'))
      | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0(B_231))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_231),u1_struct_0(B_231))))
      | ~ l1_orders_2(B_231)
      | ~ v1_lattice3(B_231)
      | ~ v5_orders_2(B_231)
      | ~ v4_orders_2(B_231)
      | ~ v3_orders_2(B_231) ) ),
    inference(resolution,[status(thm)],[c_477,c_628])).

tff(c_749,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_7'),k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_746])).

tff(c_752,plain,(
    r2_hidden('#skF_3'('#skF_6','#skF_7'),k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_50,c_101,c_749])).

tff(c_286,plain,(
    ! [A_147,B_148,C_149] :
      ( m1_subset_1(k6_waybel_4(A_147,B_148,C_149),k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_147),u1_struct_0(A_147))))
      | ~ m1_subset_1(B_148,u1_struct_0(A_147))
      | ~ l1_orders_2(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_288,plain,(
    ! [B_148] :
      ( m1_subset_1(k6_waybel_4('#skF_6',B_148,'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_286])).

tff(c_291,plain,(
    ! [B_148] :
      ( m1_subset_1(k6_waybel_4('#skF_6',B_148,'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_288])).

tff(c_292,plain,(
    ! [B_148] :
      ( m1_subset_1(k6_waybel_4('#skF_6',B_148,'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_291])).

tff(c_725,plain,(
    ! [A_224,C_225,D_226,B_227] :
      ( r2_hidden(k12_lattice3(A_224,C_225,D_226),B_227)
      | ~ r2_hidden(D_226,B_227)
      | ~ r2_hidden(C_225,B_227)
      | ~ m1_subset_1(D_226,u1_struct_0(A_224))
      | ~ m1_subset_1(C_225,u1_struct_0(A_224))
      | ~ v2_waybel_0(B_227,A_224)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ v13_waybel_0(B_227,A_224)
      | ~ l1_orders_2(A_224)
      | ~ v2_lattice3(A_224)
      | ~ v5_orders_2(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_727,plain,(
    ! [C_225,D_226,B_148] :
      ( r2_hidden(k12_lattice3('#skF_6',C_225,D_226),k6_waybel_4('#skF_6',B_148,'#skF_7'))
      | ~ r2_hidden(D_226,k6_waybel_4('#skF_6',B_148,'#skF_7'))
      | ~ r2_hidden(C_225,k6_waybel_4('#skF_6',B_148,'#skF_7'))
      | ~ m1_subset_1(D_226,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_225,u1_struct_0('#skF_6'))
      | ~ v2_waybel_0(k6_waybel_4('#skF_6',B_148,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_148,'#skF_7'),'#skF_6')
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_292,c_725])).

tff(c_1027,plain,(
    ! [C_316,D_317,B_318] :
      ( r2_hidden(k12_lattice3('#skF_6',C_316,D_317),k6_waybel_4('#skF_6',B_318,'#skF_7'))
      | ~ r2_hidden(D_317,k6_waybel_4('#skF_6',B_318,'#skF_7'))
      | ~ r2_hidden(C_316,k6_waybel_4('#skF_6',B_318,'#skF_7'))
      | ~ m1_subset_1(D_317,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_316,u1_struct_0('#skF_6'))
      | ~ v2_waybel_0(k6_waybel_4('#skF_6',B_318,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_318,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_318,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_727])).

tff(c_293,plain,(
    ! [B_150] :
      ( m1_subset_1(k6_waybel_4('#skF_6',B_150,'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_150,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_291])).

tff(c_44,plain,(
    ! [A_107,C_109,B_108] :
      ( m1_subset_1(A_107,C_109)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(C_109))
      | ~ r2_hidden(A_107,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_306,plain,(
    ! [A_107,B_150] :
      ( m1_subset_1(A_107,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_107,k6_waybel_4('#skF_6',B_150,'#skF_7'))
      | ~ m1_subset_1(B_150,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_293,c_44])).

tff(c_2242,plain,(
    ! [C_371,D_372,B_373] :
      ( m1_subset_1(k12_lattice3('#skF_6',C_371,D_372),u1_struct_0('#skF_6'))
      | ~ r2_hidden(D_372,k6_waybel_4('#skF_6',B_373,'#skF_7'))
      | ~ r2_hidden(C_371,k6_waybel_4('#skF_6',B_373,'#skF_7'))
      | ~ m1_subset_1(D_372,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_371,u1_struct_0('#skF_6'))
      | ~ v2_waybel_0(k6_waybel_4('#skF_6',B_373,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_373,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_373,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1027,c_306])).

tff(c_2250,plain,(
    ! [C_371] :
      ( m1_subset_1(k12_lattice3('#skF_6',C_371,'#skF_3'('#skF_6','#skF_7')),u1_struct_0('#skF_6'))
      | ~ r2_hidden(C_371,k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'))
      | ~ m1_subset_1('#skF_3'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_371,u1_struct_0('#skF_6'))
      | ~ v2_waybel_0(k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'),'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_752,c_2242])).

tff(c_2262,plain,(
    ! [C_371] :
      ( m1_subset_1(k12_lattice3('#skF_6',C_371,'#skF_3'('#skF_6','#skF_7')),u1_struct_0('#skF_6'))
      | ~ r2_hidden(C_371,k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'))
      | ~ m1_subset_1(C_371,u1_struct_0('#skF_6'))
      | ~ v2_waybel_0(k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_110,c_2250])).

tff(c_2266,plain,(
    ~ v13_waybel_0(k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2262])).

tff(c_2269,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_640,c_2266])).

tff(c_2273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_2269])).

tff(c_2275,plain,(
    v13_waybel_0(k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2262])).

tff(c_74,plain,(
    ! [C_117] :
      ( v5_waybel_7('#skF_7','#skF_6')
      | v2_waybel_0(k6_waybel_4('#skF_6',C_117,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(C_117,u1_struct_0('#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_82,plain,(
    ! [C_117] :
      ( v2_waybel_0(k6_waybel_4('#skF_6',C_117,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(C_117,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74])).

tff(c_2274,plain,(
    ! [C_371] :
      ( ~ v2_waybel_0(k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'),'#skF_6')
      | m1_subset_1(k12_lattice3('#skF_6',C_371,'#skF_3'('#skF_6','#skF_7')),u1_struct_0('#skF_6'))
      | ~ r2_hidden(C_371,k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'))
      | ~ m1_subset_1(C_371,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_2262])).

tff(c_2283,plain,(
    ~ v2_waybel_0(k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2274])).

tff(c_2286,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_82,c_2283])).

tff(c_2290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_2286])).

tff(c_2292,plain,(
    v2_waybel_0(k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2274])).

tff(c_111,plain,(
    ! [A_131,B_132] :
      ( m1_subset_1('#skF_2'(A_131,B_132),u1_struct_0(A_131))
      | v5_waybel_7(B_132,A_131)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_131),u1_struct_0(A_131))))
      | ~ l1_orders_2(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_114,plain,
    ( m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | v5_waybel_7('#skF_7','#skF_6')
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_111])).

tff(c_117,plain,
    ( m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | v5_waybel_7('#skF_7','#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_114])).

tff(c_118,plain,(
    m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_76,c_117])).

tff(c_314,plain,(
    ! [A_153,C_155] :
      ( k7_yellow_3(A_153,'#skF_6',C_155,'#skF_2'('#skF_6','#skF_7')) = k4_tarski(C_155,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1(C_155,u1_struct_0(A_153))
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_orders_2(A_153)
      | v2_struct_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_118,c_308])).

tff(c_325,plain,(
    ! [A_153,C_155] :
      ( k7_yellow_3(A_153,'#skF_6',C_155,'#skF_2'('#skF_6','#skF_7')) = k4_tarski(C_155,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1(C_155,u1_struct_0(A_153))
      | v2_struct_0('#skF_6')
      | ~ l1_orders_2(A_153)
      | v2_struct_0(A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_314])).

tff(c_336,plain,(
    ! [A_157,C_158] :
      ( k7_yellow_3(A_157,'#skF_6',C_158,'#skF_2'('#skF_6','#skF_7')) = k4_tarski(C_158,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1(C_158,u1_struct_0(A_157))
      | ~ l1_orders_2(A_157)
      | v2_struct_0(A_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_325])).

tff(c_351,plain,
    ( k7_yellow_3('#skF_6','#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')) = k4_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_101,c_336])).

tff(c_367,plain,
    ( k7_yellow_3('#skF_6','#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')) = k4_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_351])).

tff(c_368,plain,(
    k7_yellow_3('#skF_6','#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')) = k4_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_367])).

tff(c_482,plain,(
    ! [A_165,B_166] :
      ( r2_hidden(k7_yellow_3(A_165,A_165,'#skF_1'(A_165,B_166),'#skF_2'(A_165,B_166)),B_166)
      | v5_waybel_7(B_166,A_165)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_165),u1_struct_0(A_165))))
      | ~ l1_orders_2(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_484,plain,
    ( r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')),'#skF_7')
    | v5_waybel_7('#skF_7','#skF_6')
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_482])).

tff(c_487,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')),'#skF_7')
    | v5_waybel_7('#skF_7','#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_368,c_484])).

tff(c_488,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_76,c_487])).

tff(c_667,plain,(
    ! [B_217] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_7'),k6_waybel_4(B_217,'#skF_1'('#skF_6','#skF_7'),'#skF_7'))
      | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0(B_217))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_217),u1_struct_0(B_217))))
      | ~ l1_orders_2(B_217)
      | ~ v1_lattice3(B_217)
      | ~ v5_orders_2(B_217)
      | ~ v4_orders_2(B_217)
      | ~ v3_orders_2(B_217) ) ),
    inference(resolution,[status(thm)],[c_488,c_628])).

tff(c_670,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_7'),k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_667])).

tff(c_673,plain,(
    r2_hidden('#skF_2'('#skF_6','#skF_7'),k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_50,c_101,c_670])).

tff(c_121,plain,(
    ! [A_137,B_138,C_139] :
      ( k12_lattice3(A_137,B_138,C_139) = k11_lattice3(A_137,B_138,C_139)
      | ~ m1_subset_1(C_139,u1_struct_0(A_137))
      | ~ m1_subset_1(B_138,u1_struct_0(A_137))
      | ~ l1_orders_2(A_137)
      | ~ v2_lattice3(A_137)
      | ~ v5_orders_2(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_125,plain,(
    ! [B_138] :
      ( k12_lattice3('#skF_6',B_138,'#skF_3'('#skF_6','#skF_7')) = k11_lattice3('#skF_6',B_138,'#skF_3'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_110,c_121])).

tff(c_180,plain,(
    ! [B_142] :
      ( k12_lattice3('#skF_6',B_142,'#skF_3'('#skF_6','#skF_7')) = k11_lattice3('#skF_6',B_142,'#skF_3'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_142,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_125])).

tff(c_194,plain,(
    k12_lattice3('#skF_6','#skF_2'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7')) = k11_lattice3('#skF_6','#skF_2'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_118,c_180])).

tff(c_30,plain,(
    ! [D_81,A_74,C_79,B_75] :
      ( r2_hidden(k4_tarski(D_81,A_74),C_79)
      | ~ r2_hidden(A_74,k6_waybel_4(B_75,D_81,C_79))
      | ~ m1_subset_1(D_81,u1_struct_0(B_75))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_75),u1_struct_0(B_75))))
      | ~ l1_orders_2(B_75)
      | ~ v1_lattice3(B_75)
      | ~ v5_orders_2(B_75)
      | ~ v4_orders_2(B_75)
      | ~ v3_orders_2(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1029,plain,(
    ! [B_318,C_316,D_317] :
      ( r2_hidden(k4_tarski(B_318,k12_lattice3('#skF_6',C_316,D_317)),'#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_6'))))
      | ~ l1_orders_2('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | ~ r2_hidden(D_317,k6_waybel_4('#skF_6',B_318,'#skF_7'))
      | ~ r2_hidden(C_316,k6_waybel_4('#skF_6',B_318,'#skF_7'))
      | ~ m1_subset_1(D_317,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_316,u1_struct_0('#skF_6'))
      | ~ v2_waybel_0(k6_waybel_4('#skF_6',B_318,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_318,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_318,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1027,c_30])).

tff(c_4031,plain,(
    ! [B_406,C_407,D_408] :
      ( r2_hidden(k4_tarski(B_406,k12_lattice3('#skF_6',C_407,D_408)),'#skF_7')
      | ~ r2_hidden(D_408,k6_waybel_4('#skF_6',B_406,'#skF_7'))
      | ~ r2_hidden(C_407,k6_waybel_4('#skF_6',B_406,'#skF_7'))
      | ~ m1_subset_1(D_408,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_407,u1_struct_0('#skF_6'))
      | ~ v2_waybel_0(k6_waybel_4('#skF_6',B_406,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_406,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_406,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_50,c_46,c_1029])).

tff(c_4136,plain,(
    ! [B_406] :
      ( r2_hidden(k4_tarski(B_406,k11_lattice3('#skF_6','#skF_2'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7'))),'#skF_7')
      | ~ r2_hidden('#skF_3'('#skF_6','#skF_7'),k6_waybel_4('#skF_6',B_406,'#skF_7'))
      | ~ r2_hidden('#skF_2'('#skF_6','#skF_7'),k6_waybel_4('#skF_6',B_406,'#skF_7'))
      | ~ m1_subset_1('#skF_3'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
      | ~ v2_waybel_0(k6_waybel_4('#skF_6',B_406,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_406,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_406,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_4031])).

tff(c_6361,plain,(
    ! [B_440] :
      ( r2_hidden(k4_tarski(B_440,k11_lattice3('#skF_6','#skF_2'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7'))),'#skF_7')
      | ~ r2_hidden('#skF_3'('#skF_6','#skF_7'),k6_waybel_4('#skF_6',B_440,'#skF_7'))
      | ~ r2_hidden('#skF_2'('#skF_6','#skF_7'),k6_waybel_4('#skF_6',B_440,'#skF_7'))
      | ~ v2_waybel_0(k6_waybel_4('#skF_6',B_440,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_440,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_440,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_110,c_4136])).

tff(c_18,plain,(
    ! [A_58,B_59,C_60] :
      ( m1_subset_1(k11_lattice3(A_58,B_59,C_60),u1_struct_0(A_58))
      | ~ m1_subset_1(C_60,u1_struct_0(A_58))
      | ~ m1_subset_1(B_59,u1_struct_0(A_58))
      | ~ l1_orders_2(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_764,plain,(
    ! [A_235,A_233,C_234,B_232,C_236] :
      ( k7_yellow_3(A_235,A_233,C_234,k11_lattice3(A_233,B_232,C_236)) = k4_tarski(C_234,k11_lattice3(A_233,B_232,C_236))
      | ~ m1_subset_1(C_234,u1_struct_0(A_235))
      | v2_struct_0(A_233)
      | ~ l1_orders_2(A_235)
      | v2_struct_0(A_235)
      | ~ m1_subset_1(C_236,u1_struct_0(A_233))
      | ~ m1_subset_1(B_232,u1_struct_0(A_233))
      | ~ l1_orders_2(A_233) ) ),
    inference(resolution,[status(thm)],[c_18,c_308])).

tff(c_774,plain,(
    ! [A_233,B_232,C_236] :
      ( k7_yellow_3('#skF_6',A_233,'#skF_1'('#skF_6','#skF_7'),k11_lattice3(A_233,B_232,C_236)) = k4_tarski('#skF_1'('#skF_6','#skF_7'),k11_lattice3(A_233,B_232,C_236))
      | v2_struct_0(A_233)
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(C_236,u1_struct_0(A_233))
      | ~ m1_subset_1(B_232,u1_struct_0(A_233))
      | ~ l1_orders_2(A_233) ) ),
    inference(resolution,[status(thm)],[c_101,c_764])).

tff(c_789,plain,(
    ! [A_233,B_232,C_236] :
      ( k7_yellow_3('#skF_6',A_233,'#skF_1'('#skF_6','#skF_7'),k11_lattice3(A_233,B_232,C_236)) = k4_tarski('#skF_1'('#skF_6','#skF_7'),k11_lattice3(A_233,B_232,C_236))
      | v2_struct_0(A_233)
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(C_236,u1_struct_0(A_233))
      | ~ m1_subset_1(B_232,u1_struct_0(A_233))
      | ~ l1_orders_2(A_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_774])).

tff(c_810,plain,(
    ! [A_243,B_244,C_245] :
      ( k7_yellow_3('#skF_6',A_243,'#skF_1'('#skF_6','#skF_7'),k11_lattice3(A_243,B_244,C_245)) = k4_tarski('#skF_1'('#skF_6','#skF_7'),k11_lattice3(A_243,B_244,C_245))
      | v2_struct_0(A_243)
      | ~ m1_subset_1(C_245,u1_struct_0(A_243))
      | ~ m1_subset_1(B_244,u1_struct_0(A_243))
      | ~ l1_orders_2(A_243) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_789])).

tff(c_6,plain,(
    ! [A_2,B_32] :
      ( ~ r2_hidden(k7_yellow_3(A_2,A_2,'#skF_1'(A_2,B_32),k11_lattice3(A_2,'#skF_2'(A_2,B_32),'#skF_3'(A_2,B_32))),B_32)
      | v5_waybel_7(B_32,A_2)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2),u1_struct_0(A_2))))
      | ~ l1_orders_2(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_817,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_7'),k11_lattice3('#skF_6','#skF_2'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7'))),'#skF_7')
    | v5_waybel_7('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_6'))))
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ m1_subset_1('#skF_3'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_810,c_6])).

tff(c_823,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_7'),k11_lattice3('#skF_6','#skF_2'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7'))),'#skF_7')
    | v5_waybel_7('#skF_7','#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_118,c_110,c_50,c_46,c_817])).

tff(c_824,plain,(
    ~ r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_7'),k11_lattice3('#skF_6','#skF_2'('#skF_6','#skF_7'),'#skF_3'('#skF_6','#skF_7'))),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_76,c_823])).

tff(c_6364,plain,
    ( ~ r2_hidden('#skF_3'('#skF_6','#skF_7'),k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'))
    | ~ r2_hidden('#skF_2'('#skF_6','#skF_7'),k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'))
    | ~ v2_waybel_0(k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'),'#skF_6')
    | ~ v13_waybel_0(k6_waybel_4('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6361,c_824])).

tff(c_6370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_2275,c_2292,c_673,c_752,c_6364])).

tff(c_6372,plain,(
    v5_waybel_7('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,
    ( ~ v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ v5_waybel_7('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_6374,plain,(
    ~ v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6372,c_64])).

tff(c_6371,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_6965,plain,(
    ! [A_541,C_542,B_543] :
      ( v13_waybel_0(k6_waybel_4(A_541,C_542,B_543),A_541)
      | ~ m1_subset_1(C_542,u1_struct_0(A_541))
      | ~ m1_subset_1(B_543,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_541),u1_struct_0(A_541))))
      | ~ v5_waybel_4(B_543,A_541)
      | ~ l1_orders_2(A_541)
      | ~ v1_lattice3(A_541)
      | ~ v1_yellow_0(A_541)
      | ~ v5_orders_2(A_541)
      | ~ v4_orders_2(A_541)
      | ~ v3_orders_2(A_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6967,plain,(
    ! [C_542] :
      ( v13_waybel_0(k6_waybel_4('#skF_6',C_542,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(C_542,u1_struct_0('#skF_6'))
      | ~ v5_waybel_4('#skF_7','#skF_6')
      | ~ l1_orders_2('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v1_yellow_0('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_6965])).

tff(c_6970,plain,(
    ! [C_542] :
      ( v13_waybel_0(k6_waybel_4('#skF_6',C_542,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(C_542,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_50,c_48,c_6967])).

tff(c_6516,plain,(
    ! [A_473,B_474,C_475,D_476] :
      ( k7_yellow_3(A_473,B_474,C_475,D_476) = k4_tarski(C_475,D_476)
      | ~ m1_subset_1(D_476,u1_struct_0(B_474))
      | ~ m1_subset_1(C_475,u1_struct_0(A_473))
      | ~ l1_orders_2(B_474)
      | v2_struct_0(B_474)
      | ~ l1_orders_2(A_473)
      | v2_struct_0(A_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6524,plain,(
    ! [A_473,C_475] :
      ( k7_yellow_3(A_473,'#skF_6',C_475,'#skF_8') = k4_tarski(C_475,'#skF_8')
      | ~ m1_subset_1(C_475,u1_struct_0(A_473))
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_orders_2(A_473)
      | v2_struct_0(A_473) ) ),
    inference(resolution,[status(thm)],[c_6371,c_6516])).

tff(c_6530,plain,(
    ! [A_473,C_475] :
      ( k7_yellow_3(A_473,'#skF_6',C_475,'#skF_8') = k4_tarski(C_475,'#skF_8')
      | ~ m1_subset_1(C_475,u1_struct_0(A_473))
      | v2_struct_0('#skF_6')
      | ~ l1_orders_2(A_473)
      | v2_struct_0(A_473) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6524])).

tff(c_6531,plain,(
    v2_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6530])).

tff(c_6534,plain,
    ( ~ v2_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_6531,c_2])).

tff(c_6538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_6534])).

tff(c_6540,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_6530])).

tff(c_6541,plain,(
    ! [A_477,B_478,C_479] :
      ( m1_subset_1(k6_waybel_4(A_477,B_478,C_479),k1_zfmisc_1(u1_struct_0(A_477)))
      | ~ m1_subset_1(C_479,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_477),u1_struct_0(A_477))))
      | ~ m1_subset_1(B_478,u1_struct_0(A_477))
      | ~ l1_orders_2(A_477)
      | v2_struct_0(A_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6543,plain,(
    ! [B_478] :
      ( m1_subset_1(k6_waybel_4('#skF_6',B_478,'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_478,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_6541])).

tff(c_6546,plain,(
    ! [B_478] :
      ( m1_subset_1(k6_waybel_4('#skF_6',B_478,'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_478,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6543])).

tff(c_6548,plain,(
    ! [B_480] :
      ( m1_subset_1(k6_waybel_4('#skF_6',B_480,'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_480,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6540,c_6546])).

tff(c_36,plain,(
    ! [A_82,B_96] :
      ( r2_hidden('#skF_5'(A_82,B_96),B_96)
      | v2_waybel_0(B_96,A_82)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ v13_waybel_0(B_96,A_82)
      | ~ l1_orders_2(A_82)
      | ~ v2_lattice3(A_82)
      | ~ v5_orders_2(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_6556,plain,(
    ! [B_480] :
      ( r2_hidden('#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_480,'#skF_7')),k6_waybel_4('#skF_6',B_480,'#skF_7'))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_480,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_480,'#skF_7'),'#skF_6')
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ m1_subset_1(B_480,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6548,c_36])).

tff(c_6656,plain,(
    ! [B_495] :
      ( r2_hidden('#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_495,'#skF_7')),k6_waybel_4('#skF_6',B_495,'#skF_7'))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_495,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_495,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_495,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_6556])).

tff(c_6569,plain,(
    ! [A_107,B_480] :
      ( m1_subset_1(A_107,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_107,k6_waybel_4('#skF_6',B_480,'#skF_7'))
      | ~ m1_subset_1(B_480,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6548,c_44])).

tff(c_6660,plain,(
    ! [B_495] :
      ( m1_subset_1('#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_495,'#skF_7')),u1_struct_0('#skF_6'))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_495,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_495,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_495,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6656,c_6569])).

tff(c_7063,plain,(
    ! [A_569,C_567,A_568,C_570,B_566] :
      ( k7_yellow_3(A_569,A_568,C_567,k11_lattice3(A_568,B_566,C_570)) = k4_tarski(C_567,k11_lattice3(A_568,B_566,C_570))
      | ~ m1_subset_1(C_567,u1_struct_0(A_569))
      | v2_struct_0(A_568)
      | ~ l1_orders_2(A_569)
      | v2_struct_0(A_569)
      | ~ m1_subset_1(C_570,u1_struct_0(A_568))
      | ~ m1_subset_1(B_566,u1_struct_0(A_568))
      | ~ l1_orders_2(A_568) ) ),
    inference(resolution,[status(thm)],[c_18,c_6516])).

tff(c_7075,plain,(
    ! [A_568,B_566,C_570] :
      ( k7_yellow_3('#skF_6',A_568,'#skF_8',k11_lattice3(A_568,B_566,C_570)) = k4_tarski('#skF_8',k11_lattice3(A_568,B_566,C_570))
      | v2_struct_0(A_568)
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(C_570,u1_struct_0(A_568))
      | ~ m1_subset_1(B_566,u1_struct_0(A_568))
      | ~ l1_orders_2(A_568) ) ),
    inference(resolution,[status(thm)],[c_6371,c_7063])).

tff(c_7089,plain,(
    ! [A_568,B_566,C_570] :
      ( k7_yellow_3('#skF_6',A_568,'#skF_8',k11_lattice3(A_568,B_566,C_570)) = k4_tarski('#skF_8',k11_lattice3(A_568,B_566,C_570))
      | v2_struct_0(A_568)
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(C_570,u1_struct_0(A_568))
      | ~ m1_subset_1(B_566,u1_struct_0(A_568))
      | ~ l1_orders_2(A_568) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_7075])).

tff(c_7091,plain,(
    ! [A_571,B_572,C_573] :
      ( k7_yellow_3('#skF_6',A_571,'#skF_8',k11_lattice3(A_571,B_572,C_573)) = k4_tarski('#skF_8',k11_lattice3(A_571,B_572,C_573))
      | v2_struct_0(A_571)
      | ~ m1_subset_1(C_573,u1_struct_0(A_571))
      | ~ m1_subset_1(B_572,u1_struct_0(A_571))
      | ~ l1_orders_2(A_571) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6540,c_7089])).

tff(c_7095,plain,(
    ! [B_572,B_495] :
      ( k7_yellow_3('#skF_6','#skF_6','#skF_8',k11_lattice3('#skF_6',B_572,'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_495,'#skF_7')))) = k4_tarski('#skF_8',k11_lattice3('#skF_6',B_572,'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_495,'#skF_7'))))
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(B_572,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | v2_waybel_0(k6_waybel_4('#skF_6',B_495,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_495,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_495,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6660,c_7091])).

tff(c_7110,plain,(
    ! [B_572,B_495] :
      ( k7_yellow_3('#skF_6','#skF_6','#skF_8',k11_lattice3('#skF_6',B_572,'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_495,'#skF_7')))) = k4_tarski('#skF_8',k11_lattice3('#skF_6',B_572,'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_495,'#skF_7'))))
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(B_572,u1_struct_0('#skF_6'))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_495,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_495,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_495,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_7095])).

tff(c_7638,plain,(
    ! [B_684,B_685] :
      ( k7_yellow_3('#skF_6','#skF_6','#skF_8',k11_lattice3('#skF_6',B_684,'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_685,'#skF_7')))) = k4_tarski('#skF_8',k11_lattice3('#skF_6',B_684,'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_685,'#skF_7'))))
      | ~ m1_subset_1(B_684,u1_struct_0('#skF_6'))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_685,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_685,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_685,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6540,c_7110])).

tff(c_7185,plain,(
    ! [D_582,C_583,A_584,E_581,B_580] :
      ( r2_hidden(k7_yellow_3(A_584,A_584,C_583,k11_lattice3(A_584,D_582,E_581)),B_580)
      | ~ r2_hidden(k7_yellow_3(A_584,A_584,C_583,E_581),B_580)
      | ~ r2_hidden(k7_yellow_3(A_584,A_584,C_583,D_582),B_580)
      | ~ m1_subset_1(E_581,u1_struct_0(A_584))
      | ~ m1_subset_1(D_582,u1_struct_0(A_584))
      | ~ m1_subset_1(C_583,u1_struct_0(A_584))
      | ~ v5_waybel_7(B_580,A_584)
      | ~ m1_subset_1(B_580,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_584),u1_struct_0(A_584))))
      | ~ l1_orders_2(A_584)
      | v2_struct_0(A_584) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_7187,plain,(
    ! [C_583,D_582,E_581] :
      ( r2_hidden(k7_yellow_3('#skF_6','#skF_6',C_583,k11_lattice3('#skF_6',D_582,E_581)),'#skF_7')
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6',C_583,E_581),'#skF_7')
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6',C_583,D_582),'#skF_7')
      | ~ m1_subset_1(E_581,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(D_582,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_583,u1_struct_0('#skF_6'))
      | ~ v5_waybel_7('#skF_7','#skF_6')
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_7185])).

tff(c_7190,plain,(
    ! [C_583,D_582,E_581] :
      ( r2_hidden(k7_yellow_3('#skF_6','#skF_6',C_583,k11_lattice3('#skF_6',D_582,E_581)),'#skF_7')
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6',C_583,E_581),'#skF_7')
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6',C_583,D_582),'#skF_7')
      | ~ m1_subset_1(E_581,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(D_582,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_583,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6372,c_7187])).

tff(c_7191,plain,(
    ! [C_583,D_582,E_581] :
      ( r2_hidden(k7_yellow_3('#skF_6','#skF_6',C_583,k11_lattice3('#skF_6',D_582,E_581)),'#skF_7')
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6',C_583,E_581),'#skF_7')
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6',C_583,D_582),'#skF_7')
      | ~ m1_subset_1(E_581,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(D_582,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_583,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6540,c_7190])).

tff(c_7644,plain,(
    ! [B_684,B_685] :
      ( r2_hidden(k4_tarski('#skF_8',k11_lattice3('#skF_6',B_684,'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_685,'#skF_7')))),'#skF_7')
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_685,'#skF_7'))),'#skF_7')
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8',B_684),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_685,'#skF_7')),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_684,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_684,u1_struct_0('#skF_6'))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_685,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_685,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_685,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7638,c_7191])).

tff(c_8665,plain,(
    ! [B_825,B_826] :
      ( r2_hidden(k4_tarski('#skF_8',k11_lattice3('#skF_6',B_825,'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_826,'#skF_7')))),'#skF_7')
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_826,'#skF_7'))),'#skF_7')
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8',B_825),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_826,'#skF_7')),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_825,u1_struct_0('#skF_6'))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_826,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_826,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_826,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6371,c_7644])).

tff(c_28,plain,(
    ! [A_74,B_75,D_81,C_79] :
      ( r2_hidden(A_74,k6_waybel_4(B_75,D_81,C_79))
      | ~ r2_hidden(k4_tarski(D_81,A_74),C_79)
      | ~ m1_subset_1(D_81,u1_struct_0(B_75))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_75),u1_struct_0(B_75))))
      | ~ l1_orders_2(B_75)
      | ~ v1_lattice3(B_75)
      | ~ v5_orders_2(B_75)
      | ~ v4_orders_2(B_75)
      | ~ v3_orders_2(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_68893,plain,(
    ! [B_2331,B_2332,B_2333] :
      ( r2_hidden(k11_lattice3('#skF_6',B_2331,'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_2332,'#skF_7'))),k6_waybel_4(B_2333,'#skF_8','#skF_7'))
      | ~ m1_subset_1('#skF_8',u1_struct_0(B_2333))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_2333),u1_struct_0(B_2333))))
      | ~ l1_orders_2(B_2333)
      | ~ v1_lattice3(B_2333)
      | ~ v5_orders_2(B_2333)
      | ~ v4_orders_2(B_2333)
      | ~ v3_orders_2(B_2333)
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_2332,'#skF_7'))),'#skF_7')
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8',B_2331),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_2332,'#skF_7')),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_2331,u1_struct_0('#skF_6'))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_2332,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_2332,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_2332,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_8665,c_28])).

tff(c_68895,plain,(
    ! [B_2331,B_2332] :
      ( r2_hidden(k11_lattice3('#skF_6',B_2331,'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_2332,'#skF_7'))),k6_waybel_4('#skF_6','#skF_8','#skF_7'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_2332,'#skF_7'))),'#skF_7')
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8',B_2331),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_2332,'#skF_7')),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_2331,u1_struct_0('#skF_6'))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_2332,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_2332,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_2332,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_46,c_68893])).

tff(c_68899,plain,(
    ! [B_2334,B_2335] :
      ( r2_hidden(k11_lattice3('#skF_6',B_2334,'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_2335,'#skF_7'))),k6_waybel_4('#skF_6','#skF_8','#skF_7'))
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_2335,'#skF_7'))),'#skF_7')
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8',B_2334),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_2335,'#skF_7')),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_2334,u1_struct_0('#skF_6'))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_2335,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_2335,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_2335,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_50,c_6371,c_68895])).

tff(c_6547,plain,(
    ! [B_478] :
      ( m1_subset_1(k6_waybel_4('#skF_6',B_478,'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_478,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6540,c_6546])).

tff(c_42,plain,(
    ! [A_82,B_96] :
      ( m1_subset_1('#skF_4'(A_82,B_96),u1_struct_0(A_82))
      | v2_waybel_0(B_96,A_82)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ v13_waybel_0(B_96,A_82)
      | ~ l1_orders_2(A_82)
      | ~ v2_lattice3(A_82)
      | ~ v5_orders_2(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_6441,plain,(
    ! [A_464,B_465] :
      ( m1_subset_1('#skF_5'(A_464,B_465),u1_struct_0(A_464))
      | v2_waybel_0(B_465,A_464)
      | ~ m1_subset_1(B_465,k1_zfmisc_1(u1_struct_0(A_464)))
      | ~ v13_waybel_0(B_465,A_464)
      | ~ l1_orders_2(A_464)
      | ~ v2_lattice3(A_464)
      | ~ v5_orders_2(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_24,plain,(
    ! [A_67,B_68,C_69] :
      ( k12_lattice3(A_67,B_68,C_69) = k11_lattice3(A_67,B_68,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(A_67))
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l1_orders_2(A_67)
      | ~ v2_lattice3(A_67)
      | ~ v5_orders_2(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_7011,plain,(
    ! [A_550,B_551,B_552] :
      ( k12_lattice3(A_550,B_551,'#skF_5'(A_550,B_552)) = k11_lattice3(A_550,B_551,'#skF_5'(A_550,B_552))
      | ~ m1_subset_1(B_551,u1_struct_0(A_550))
      | v2_waybel_0(B_552,A_550)
      | ~ m1_subset_1(B_552,k1_zfmisc_1(u1_struct_0(A_550)))
      | ~ v13_waybel_0(B_552,A_550)
      | ~ l1_orders_2(A_550)
      | ~ v2_lattice3(A_550)
      | ~ v5_orders_2(A_550) ) ),
    inference(resolution,[status(thm)],[c_6441,c_24])).

tff(c_7600,plain,(
    ! [A_670,B_671,B_672] :
      ( k12_lattice3(A_670,'#skF_4'(A_670,B_671),'#skF_5'(A_670,B_672)) = k11_lattice3(A_670,'#skF_4'(A_670,B_671),'#skF_5'(A_670,B_672))
      | v2_waybel_0(B_672,A_670)
      | ~ m1_subset_1(B_672,k1_zfmisc_1(u1_struct_0(A_670)))
      | ~ v13_waybel_0(B_672,A_670)
      | v2_waybel_0(B_671,A_670)
      | ~ m1_subset_1(B_671,k1_zfmisc_1(u1_struct_0(A_670)))
      | ~ v13_waybel_0(B_671,A_670)
      | ~ l1_orders_2(A_670)
      | ~ v2_lattice3(A_670)
      | ~ v5_orders_2(A_670) ) ),
    inference(resolution,[status(thm)],[c_42,c_7011])).

tff(c_7602,plain,(
    ! [B_671,B_478] :
      ( k12_lattice3('#skF_6','#skF_4'('#skF_6',B_671),'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_478,'#skF_7'))) = k11_lattice3('#skF_6','#skF_4'('#skF_6',B_671),'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_478,'#skF_7')))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_478,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_478,'#skF_7'),'#skF_6')
      | v2_waybel_0(B_671,'#skF_6')
      | ~ m1_subset_1(B_671,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v13_waybel_0(B_671,'#skF_6')
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ m1_subset_1(B_478,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6547,c_7600])).

tff(c_8064,plain,(
    ! [B_742,B_743] :
      ( k12_lattice3('#skF_6','#skF_4'('#skF_6',B_742),'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_743,'#skF_7'))) = k11_lattice3('#skF_6','#skF_4'('#skF_6',B_742),'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_743,'#skF_7')))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_743,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_743,'#skF_7'),'#skF_6')
      | v2_waybel_0(B_742,'#skF_6')
      | ~ m1_subset_1(B_742,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v13_waybel_0(B_742,'#skF_6')
      | ~ m1_subset_1(B_743,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_7602])).

tff(c_34,plain,(
    ! [A_82,B_96] :
      ( ~ r2_hidden(k12_lattice3(A_82,'#skF_4'(A_82,B_96),'#skF_5'(A_82,B_96)),B_96)
      | v2_waybel_0(B_96,A_82)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ v13_waybel_0(B_96,A_82)
      | ~ l1_orders_2(A_82)
      | ~ v2_lattice3(A_82)
      | ~ v5_orders_2(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_8080,plain,(
    ! [B_743] :
      ( ~ r2_hidden(k11_lattice3('#skF_6','#skF_4'('#skF_6',k6_waybel_4('#skF_6',B_743,'#skF_7')),'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_743,'#skF_7'))),k6_waybel_4('#skF_6',B_743,'#skF_7'))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_743,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(k6_waybel_4('#skF_6',B_743,'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_743,'#skF_7'),'#skF_6')
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | v2_waybel_0(k6_waybel_4('#skF_6',B_743,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_743,'#skF_7'),'#skF_6')
      | v2_waybel_0(k6_waybel_4('#skF_6',B_743,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(k6_waybel_4('#skF_6',B_743,'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_743,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_743,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8064,c_34])).

tff(c_8091,plain,(
    ! [B_743] :
      ( ~ r2_hidden(k11_lattice3('#skF_6','#skF_4'('#skF_6',k6_waybel_4('#skF_6',B_743,'#skF_7')),'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_743,'#skF_7'))),k6_waybel_4('#skF_6',B_743,'#skF_7'))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_743,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(k6_waybel_4('#skF_6',B_743,'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_743,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_743,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_8080])).

tff(c_68989,plain,
    ( ~ m1_subset_1(k6_waybel_4('#skF_6','#skF_8','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),'#skF_7')
    | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6'))
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ v13_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_68899,c_8091])).

tff(c_69128,plain,
    ( ~ m1_subset_1(k6_waybel_4('#skF_6','#skF_8','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),'#skF_7')
    | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6'))
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ v13_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6371,c_68989])).

tff(c_69129,plain,
    ( ~ m1_subset_1(k6_waybel_4('#skF_6','#skF_8','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),'#skF_7')
    | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6'))
    | ~ v13_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_6374,c_69128])).

tff(c_69139,plain,(
    ~ v13_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_69129])).

tff(c_69142,plain,(
    ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6970,c_69139])).

tff(c_69146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6371,c_69142])).

tff(c_69148,plain,(
    v13_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_69129])).

tff(c_38,plain,(
    ! [A_82,B_96] :
      ( r2_hidden('#skF_4'(A_82,B_96),B_96)
      | v2_waybel_0(B_96,A_82)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ v13_waybel_0(B_96,A_82)
      | ~ l1_orders_2(A_82)
      | ~ v2_lattice3(A_82)
      | ~ v5_orders_2(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_6558,plain,(
    ! [B_480] :
      ( r2_hidden('#skF_4'('#skF_6',k6_waybel_4('#skF_6',B_480,'#skF_7')),k6_waybel_4('#skF_6',B_480,'#skF_7'))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_480,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_480,'#skF_7'),'#skF_6')
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ m1_subset_1(B_480,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6548,c_38])).

tff(c_6568,plain,(
    ! [B_480] :
      ( r2_hidden('#skF_4'('#skF_6',k6_waybel_4('#skF_6',B_480,'#skF_7')),k6_waybel_4('#skF_6',B_480,'#skF_7'))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_480,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_480,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_480,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_6558])).

tff(c_69147,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6'))
    | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),'#skF_7')
    | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),'#skF_7')
    | ~ m1_subset_1(k6_waybel_4('#skF_6','#skF_8','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_69129])).

tff(c_69149,plain,(
    ~ m1_subset_1(k6_waybel_4('#skF_6','#skF_8','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_69147])).

tff(c_69152,plain,(
    ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6547,c_69149])).

tff(c_69156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6371,c_69152])).

tff(c_69158,plain,(
    m1_subset_1(k6_waybel_4('#skF_6','#skF_8','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_69147])).

tff(c_69483,plain,(
    ! [A_2336] :
      ( m1_subset_1(A_2336,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_2336,k6_waybel_4('#skF_6','#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_69158,c_44])).

tff(c_69632,plain,
    ( m1_subset_1('#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6'))
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ v13_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6568,c_69483])).

tff(c_69744,plain,
    ( m1_subset_1('#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6'))
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6371,c_69148,c_69632])).

tff(c_69745,plain,(
    m1_subset_1('#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_6374,c_69744])).

tff(c_6565,plain,(
    ! [B_480] :
      ( r2_hidden('#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_480,'#skF_7')),k6_waybel_4('#skF_6',B_480,'#skF_7'))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_480,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_480,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_480,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_6556])).

tff(c_69636,plain,
    ( m1_subset_1('#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6'))
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ v13_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6565,c_69483])).

tff(c_69748,plain,
    ( m1_subset_1('#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6'))
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6371,c_69148,c_69636])).

tff(c_69749,plain,(
    m1_subset_1('#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_6374,c_69748])).

tff(c_69276,plain,
    ( r2_hidden('#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),k6_waybel_4('#skF_6','#skF_8','#skF_7'))
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ v13_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_69158,c_38])).

tff(c_69480,plain,
    ( r2_hidden('#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),k6_waybel_4('#skF_6','#skF_8','#skF_7'))
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_69148,c_69276])).

tff(c_69481,plain,(
    r2_hidden('#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),k6_waybel_4('#skF_6','#skF_8','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_6374,c_69480])).

tff(c_70146,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),'#skF_7')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_6'))))
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_69481,c_30])).

tff(c_70225,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_50,c_46,c_6371,c_70146])).

tff(c_7257,plain,(
    ! [A_593,A_594,C_595,B_596] :
      ( k7_yellow_3(A_593,A_594,C_595,'#skF_4'(A_594,B_596)) = k4_tarski(C_595,'#skF_4'(A_594,B_596))
      | ~ m1_subset_1(C_595,u1_struct_0(A_593))
      | v2_struct_0(A_594)
      | ~ l1_orders_2(A_593)
      | v2_struct_0(A_593)
      | v2_waybel_0(B_596,A_594)
      | ~ m1_subset_1(B_596,k1_zfmisc_1(u1_struct_0(A_594)))
      | ~ v13_waybel_0(B_596,A_594)
      | ~ l1_orders_2(A_594)
      | ~ v2_lattice3(A_594)
      | ~ v5_orders_2(A_594) ) ),
    inference(resolution,[status(thm)],[c_42,c_6516])).

tff(c_7269,plain,(
    ! [A_594,B_596] :
      ( k7_yellow_3('#skF_6',A_594,'#skF_8','#skF_4'(A_594,B_596)) = k4_tarski('#skF_8','#skF_4'(A_594,B_596))
      | v2_struct_0(A_594)
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | v2_waybel_0(B_596,A_594)
      | ~ m1_subset_1(B_596,k1_zfmisc_1(u1_struct_0(A_594)))
      | ~ v13_waybel_0(B_596,A_594)
      | ~ l1_orders_2(A_594)
      | ~ v2_lattice3(A_594)
      | ~ v5_orders_2(A_594) ) ),
    inference(resolution,[status(thm)],[c_6371,c_7257])).

tff(c_7283,plain,(
    ! [A_594,B_596] :
      ( k7_yellow_3('#skF_6',A_594,'#skF_8','#skF_4'(A_594,B_596)) = k4_tarski('#skF_8','#skF_4'(A_594,B_596))
      | v2_struct_0(A_594)
      | v2_struct_0('#skF_6')
      | v2_waybel_0(B_596,A_594)
      | ~ m1_subset_1(B_596,k1_zfmisc_1(u1_struct_0(A_594)))
      | ~ v13_waybel_0(B_596,A_594)
      | ~ l1_orders_2(A_594)
      | ~ v2_lattice3(A_594)
      | ~ v5_orders_2(A_594) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_7269])).

tff(c_7284,plain,(
    ! [A_594,B_596] :
      ( k7_yellow_3('#skF_6',A_594,'#skF_8','#skF_4'(A_594,B_596)) = k4_tarski('#skF_8','#skF_4'(A_594,B_596))
      | v2_struct_0(A_594)
      | v2_waybel_0(B_596,A_594)
      | ~ m1_subset_1(B_596,k1_zfmisc_1(u1_struct_0(A_594)))
      | ~ v13_waybel_0(B_596,A_594)
      | ~ l1_orders_2(A_594)
      | ~ v2_lattice3(A_594)
      | ~ v5_orders_2(A_594) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6540,c_7283])).

tff(c_69222,plain,
    ( k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))) = k4_tarski('#skF_8','#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')))
    | v2_struct_0('#skF_6')
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ v13_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_69158,c_7284])).

tff(c_69397,plain,
    ( k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))) = k4_tarski('#skF_8','#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')))
    | v2_struct_0('#skF_6')
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_69148,c_69222])).

tff(c_69398,plain,(
    k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))) = k4_tarski('#skF_8','#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6374,c_6540,c_69397])).

tff(c_69274,plain,
    ( r2_hidden('#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),k6_waybel_4('#skF_6','#skF_8','#skF_7'))
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ v13_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_69158,c_36])).

tff(c_69476,plain,
    ( r2_hidden('#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),k6_waybel_4('#skF_6','#skF_8','#skF_7'))
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_69148,c_69274])).

tff(c_69477,plain,(
    r2_hidden('#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),k6_waybel_4('#skF_6','#skF_8','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_6374,c_69476])).

tff(c_70006,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),'#skF_7')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_6'))))
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_69477,c_30])).

tff(c_70089,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_50,c_46,c_6371,c_70006])).

tff(c_40,plain,(
    ! [A_82,B_96] :
      ( m1_subset_1('#skF_5'(A_82,B_96),u1_struct_0(A_82))
      | v2_waybel_0(B_96,A_82)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ v13_waybel_0(B_96,A_82)
      | ~ l1_orders_2(A_82)
      | ~ v2_lattice3(A_82)
      | ~ v5_orders_2(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_7354,plain,(
    ! [A_610,A_611,C_612,B_613] :
      ( k7_yellow_3(A_610,A_611,C_612,'#skF_5'(A_611,B_613)) = k4_tarski(C_612,'#skF_5'(A_611,B_613))
      | ~ m1_subset_1(C_612,u1_struct_0(A_610))
      | v2_struct_0(A_611)
      | ~ l1_orders_2(A_610)
      | v2_struct_0(A_610)
      | v2_waybel_0(B_613,A_611)
      | ~ m1_subset_1(B_613,k1_zfmisc_1(u1_struct_0(A_611)))
      | ~ v13_waybel_0(B_613,A_611)
      | ~ l1_orders_2(A_611)
      | ~ v2_lattice3(A_611)
      | ~ v5_orders_2(A_611) ) ),
    inference(resolution,[status(thm)],[c_40,c_6516])).

tff(c_7366,plain,(
    ! [A_611,B_613] :
      ( k7_yellow_3('#skF_6',A_611,'#skF_8','#skF_5'(A_611,B_613)) = k4_tarski('#skF_8','#skF_5'(A_611,B_613))
      | v2_struct_0(A_611)
      | ~ l1_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | v2_waybel_0(B_613,A_611)
      | ~ m1_subset_1(B_613,k1_zfmisc_1(u1_struct_0(A_611)))
      | ~ v13_waybel_0(B_613,A_611)
      | ~ l1_orders_2(A_611)
      | ~ v2_lattice3(A_611)
      | ~ v5_orders_2(A_611) ) ),
    inference(resolution,[status(thm)],[c_6371,c_7354])).

tff(c_7380,plain,(
    ! [A_611,B_613] :
      ( k7_yellow_3('#skF_6',A_611,'#skF_8','#skF_5'(A_611,B_613)) = k4_tarski('#skF_8','#skF_5'(A_611,B_613))
      | v2_struct_0(A_611)
      | v2_struct_0('#skF_6')
      | v2_waybel_0(B_613,A_611)
      | ~ m1_subset_1(B_613,k1_zfmisc_1(u1_struct_0(A_611)))
      | ~ v13_waybel_0(B_613,A_611)
      | ~ l1_orders_2(A_611)
      | ~ v2_lattice3(A_611)
      | ~ v5_orders_2(A_611) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_7366])).

tff(c_7381,plain,(
    ! [A_611,B_613] :
      ( k7_yellow_3('#skF_6',A_611,'#skF_8','#skF_5'(A_611,B_613)) = k4_tarski('#skF_8','#skF_5'(A_611,B_613))
      | v2_struct_0(A_611)
      | v2_waybel_0(B_613,A_611)
      | ~ m1_subset_1(B_613,k1_zfmisc_1(u1_struct_0(A_611)))
      | ~ v13_waybel_0(B_613,A_611)
      | ~ l1_orders_2(A_611)
      | ~ v2_lattice3(A_611)
      | ~ v5_orders_2(A_611) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6540,c_7380])).

tff(c_69220,plain,
    ( k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))) = k4_tarski('#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')))
    | v2_struct_0('#skF_6')
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ v13_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_69158,c_7381])).

tff(c_69393,plain,
    ( k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))) = k4_tarski('#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')))
    | v2_struct_0('#skF_6')
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_69148,c_69220])).

tff(c_69394,plain,(
    k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))) = k4_tarski('#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6374,c_6540,c_69393])).

tff(c_68898,plain,(
    ! [B_2331,B_2332] :
      ( r2_hidden(k11_lattice3('#skF_6',B_2331,'#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_2332,'#skF_7'))),k6_waybel_4('#skF_6','#skF_8','#skF_7'))
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_2332,'#skF_7'))),'#skF_7')
      | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8',B_2331),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_6',k6_waybel_4('#skF_6',B_2332,'#skF_7')),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_2331,u1_struct_0('#skF_6'))
      | v2_waybel_0(k6_waybel_4('#skF_6',B_2332,'#skF_7'),'#skF_6')
      | ~ v13_waybel_0(k6_waybel_4('#skF_6',B_2332,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(B_2332,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_50,c_6371,c_68895])).

tff(c_69901,plain,(
    ! [B_68] :
      ( k12_lattice3('#skF_6',B_68,'#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))) = k11_lattice3('#skF_6',B_68,'#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')))
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_69749,c_24])).

tff(c_70513,plain,(
    ! [B_2343] :
      ( k12_lattice3('#skF_6',B_2343,'#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))) = k11_lattice3('#skF_6',B_2343,'#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')))
      | ~ m1_subset_1(B_2343,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_69901])).

tff(c_70628,plain,
    ( ~ r2_hidden(k11_lattice3('#skF_6','#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),'#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),k6_waybel_4('#skF_6','#skF_8','#skF_7'))
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ m1_subset_1(k6_waybel_4('#skF_6','#skF_8','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v13_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ m1_subset_1('#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70513,c_34])).

tff(c_70844,plain,
    ( ~ r2_hidden(k11_lattice3('#skF_6','#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),'#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),k6_waybel_4('#skF_6','#skF_8','#skF_7'))
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69745,c_58,c_52,c_50,c_69148,c_69158,c_70628])).

tff(c_70845,plain,(
    ~ r2_hidden(k11_lattice3('#skF_6','#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),'#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),k6_waybel_4('#skF_6','#skF_8','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_6374,c_70844])).

tff(c_70962,plain,
    ( ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),'#skF_7')
    | ~ r2_hidden(k7_yellow_3('#skF_6','#skF_6','#skF_8','#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7'))),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_4'('#skF_6',k6_waybel_4('#skF_6','#skF_8','#skF_7')),u1_struct_0('#skF_6'))
    | v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ v13_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_68898,c_70845])).

tff(c_70974,plain,(
    v2_waybel_0(k6_waybel_4('#skF_6','#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6371,c_69148,c_69745,c_69749,c_70225,c_69398,c_70089,c_69394,c_70962])).

tff(c_70976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6374,c_70974])).

%------------------------------------------------------------------------------
