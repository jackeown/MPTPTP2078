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
% DateTime   : Thu Dec  3 10:24:38 EST 2020

% Result     : Theorem 10.64s
% Output     : CNFRefutation 10.97s
% Verified   : 
% Statistics : Number of formulae       :  305 (8363 expanded)
%              Number of leaves         :   54 (2938 expanded)
%              Depth                    :   42
%              Number of atoms          : 1018 (34638 expanded)
%              Number of equality atoms :  193 (3431 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r3_lattices > r1_orders_2 > v1_partfun1 > v19_lattices > v18_lattices > r2_hidden > m1_subset_1 > v8_relat_2 > v5_orders_2 > v4_relat_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_2 > v1_orders_2 > v10_lattices > l3_lattices > l1_orders_2 > k1_domain_1 > k4_tarski > k4_lattice3 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k8_filter_1 > k3_lattice3 > k2_lattice3 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_domain_1,type,(
    k1_domain_1: ( $i * $i * $i * $i ) > $i )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k4_lattice3,type,(
    k4_lattice3: ( $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v19_lattices,type,(
    v19_lattices: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v18_lattices,type,(
    v18_lattices: ( $i * $i ) > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k8_filter_1,type,(
    k8_filter_1: $i > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_lattice3,type,(
    k2_lattice3: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_231,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r3_lattices(A,B,C)
                <=> r3_orders_2(k3_lattice3(A),k4_lattice3(A,B),k4_lattice3(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_lattice3)).

tff(f_175,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ( v1_orders_2(k3_lattice3(A))
        & v3_orders_2(k3_lattice3(A))
        & v4_orders_2(k3_lattice3(A))
        & v5_orders_2(k3_lattice3(A))
        & l1_orders_2(k3_lattice3(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_lattice3)).

tff(f_204,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ( ~ v2_struct_0(k3_lattice3(A))
        & v1_orders_2(k3_lattice3(A))
        & v3_orders_2(k3_lattice3(A))
        & v4_orders_2(k3_lattice3(A))
        & v5_orders_2(k3_lattice3(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_lattice3)).

tff(f_141,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k4_lattice3(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattice3)).

tff(f_186,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k4_lattice3(A,B),u1_struct_0(k3_lattice3(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattice3)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_158,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ( v1_partfun1(k2_lattice3(A),u1_struct_0(A))
        & v1_relat_2(k2_lattice3(A))
        & v4_relat_2(k2_lattice3(A))
        & v8_relat_2(k2_lattice3(A))
        & m1_subset_1(k2_lattice3(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattice3)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => k3_lattice3(A) = g1_orders_2(u1_struct_0(A),k2_lattice3(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_lattice3)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(C,A)
        & m1_subset_1(D,B) )
     => k1_domain_1(A,B,C,D) = k4_tarski(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_domain_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v18_lattices(B,A)
          & v19_lattices(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc14_lattices)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_213,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => k2_lattice3(A) = k8_filter_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_lattice3)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(k1_domain_1(u1_struct_0(A),u1_struct_0(A),B,C),k8_filter_1(A))
              <=> r3_lattices(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_filter_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_86,plain,
    ( r3_lattices('#skF_2','#skF_3','#skF_4')
    | r3_orders_2(k3_lattice3('#skF_2'),k4_lattice3('#skF_2','#skF_3'),k4_lattice3('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_91,plain,(
    r3_orders_2(k3_lattice3('#skF_2'),k4_lattice3('#skF_2','#skF_3'),k4_lattice3('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_80,plain,
    ( ~ r3_orders_2(k3_lattice3('#skF_2'),k4_lattice3('#skF_2','#skF_3'),k4_lattice3('#skF_2','#skF_4'))
    | ~ r3_lattices('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_101,plain,(
    ~ r3_lattices('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_80])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_76,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_74,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_46,plain,(
    ! [A_39] :
      ( l1_orders_2(k3_lattice3(A_39))
      | ~ l3_lattices(A_39)
      | ~ v10_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_62,plain,(
    ! [A_42] :
      ( v3_orders_2(k3_lattice3(A_42))
      | ~ l3_lattices(A_42)
      | ~ v10_lattices(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_143,plain,(
    ! [A_68,B_69] :
      ( k4_lattice3(A_68,B_69) = B_69
      | ~ m1_subset_1(B_69,u1_struct_0(A_68))
      | ~ l3_lattices(A_68)
      | ~ v10_lattices(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_149,plain,
    ( k4_lattice3('#skF_2','#skF_3') = '#skF_3'
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_143])).

tff(c_156,plain,
    ( k4_lattice3('#skF_2','#skF_3') = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_149])).

tff(c_157,plain,(
    k4_lattice3('#skF_2','#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_156])).

tff(c_199,plain,(
    ! [A_79,B_80] :
      ( m1_subset_1(k4_lattice3(A_79,B_80),u1_struct_0(k3_lattice3(A_79)))
      | ~ m1_subset_1(B_80,u1_struct_0(A_79))
      | ~ l3_lattices(A_79)
      | ~ v10_lattices(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_205,plain,
    ( m1_subset_1('#skF_3',u1_struct_0(k3_lattice3('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_199])).

tff(c_211,plain,
    ( m1_subset_1('#skF_3',u1_struct_0(k3_lattice3('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_205])).

tff(c_212,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k3_lattice3('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_211])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_146,plain,
    ( k4_lattice3('#skF_2','#skF_4') = '#skF_4'
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_143])).

tff(c_152,plain,
    ( k4_lattice3('#skF_2','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_146])).

tff(c_153,plain,(
    k4_lattice3('#skF_2','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_152])).

tff(c_208,plain,
    ( m1_subset_1('#skF_4',u1_struct_0(k3_lattice3('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_199])).

tff(c_214,plain,
    ( m1_subset_1('#skF_4',u1_struct_0(k3_lattice3('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_208])).

tff(c_215,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k3_lattice3('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_214])).

tff(c_158,plain,(
    r3_orders_2(k3_lattice3('#skF_2'),k4_lattice3('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_91])).

tff(c_167,plain,(
    r3_orders_2(k3_lattice3('#skF_2'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_158])).

tff(c_861,plain,(
    ! [A_179,B_180,C_181] :
      ( r1_orders_2(A_179,B_180,C_181)
      | ~ r3_orders_2(A_179,B_180,C_181)
      | ~ m1_subset_1(C_181,u1_struct_0(A_179))
      | ~ m1_subset_1(B_180,u1_struct_0(A_179))
      | ~ l1_orders_2(A_179)
      | ~ v3_orders_2(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_863,plain,
    ( r1_orders_2(k3_lattice3('#skF_2'),'#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0(k3_lattice3('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k3_lattice3('#skF_2')))
    | ~ l1_orders_2(k3_lattice3('#skF_2'))
    | ~ v3_orders_2(k3_lattice3('#skF_2'))
    | v2_struct_0(k3_lattice3('#skF_2')) ),
    inference(resolution,[status(thm)],[c_167,c_861])).

tff(c_866,plain,
    ( r1_orders_2(k3_lattice3('#skF_2'),'#skF_3','#skF_4')
    | ~ l1_orders_2(k3_lattice3('#skF_2'))
    | ~ v3_orders_2(k3_lattice3('#skF_2'))
    | v2_struct_0(k3_lattice3('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_215,c_863])).

tff(c_867,plain,(
    ~ v3_orders_2(k3_lattice3('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_866])).

tff(c_870,plain,
    ( ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_867])).

tff(c_873,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_870])).

tff(c_875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_873])).

tff(c_876,plain,
    ( ~ l1_orders_2(k3_lattice3('#skF_2'))
    | v2_struct_0(k3_lattice3('#skF_2'))
    | r1_orders_2(k3_lattice3('#skF_2'),'#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_866])).

tff(c_878,plain,(
    ~ l1_orders_2(k3_lattice3('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_876])).

tff(c_881,plain,
    ( ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_878])).

tff(c_884,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_881])).

tff(c_886,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_884])).

tff(c_887,plain,
    ( r1_orders_2(k3_lattice3('#skF_2'),'#skF_3','#skF_4')
    | v2_struct_0(k3_lattice3('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_876])).

tff(c_913,plain,(
    v2_struct_0(k3_lattice3('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_887])).

tff(c_66,plain,(
    ! [A_42] :
      ( ~ v2_struct_0(k3_lattice3(A_42))
      | ~ l3_lattices(A_42)
      | ~ v10_lattices(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_916,plain,
    ( ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_913,c_66])).

tff(c_919,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_916])).

tff(c_921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_919])).

tff(c_922,plain,(
    r1_orders_2(k3_lattice3('#skF_2'),'#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_887])).

tff(c_64,plain,(
    ! [A_42] :
      ( v1_orders_2(k3_lattice3(A_42))
      | ~ l3_lattices(A_42)
      | ~ v10_lattices(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_36,plain,(
    ! [A_38] :
      ( m1_subset_1(k2_lattice3(A_38),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38),u1_struct_0(A_38))))
      | ~ l3_lattices(A_38)
      | ~ v10_lattices(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_4,plain,(
    ! [A_4] :
      ( g1_orders_2(u1_struct_0(A_4),u1_orders_2(A_4)) = A_4
      | ~ v1_orders_2(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    ! [A_34] :
      ( g1_orders_2(u1_struct_0(A_34),k2_lattice3(A_34)) = k3_lattice3(A_34)
      | ~ l3_lattices(A_34)
      | ~ v10_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_185,plain,(
    ! [C_74,A_75,D_76,B_77] :
      ( C_74 = A_75
      | g1_orders_2(C_74,D_76) != g1_orders_2(A_75,B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_zfmisc_1(A_75,A_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1143,plain,(
    ! [A_209,C_210,D_211] :
      ( u1_struct_0(A_209) = C_210
      | k3_lattice3(A_209) != g1_orders_2(C_210,D_211)
      | ~ m1_subset_1(k2_lattice3(A_209),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_209),u1_struct_0(A_209))))
      | ~ l3_lattices(A_209)
      | ~ v10_lattices(A_209)
      | v2_struct_0(A_209) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_185])).

tff(c_1159,plain,(
    ! [A_218,A_217] :
      ( u1_struct_0(A_218) = u1_struct_0(A_217)
      | k3_lattice3(A_218) != A_217
      | ~ m1_subset_1(k2_lattice3(A_218),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_218),u1_struct_0(A_218))))
      | ~ l3_lattices(A_218)
      | ~ v10_lattices(A_218)
      | v2_struct_0(A_218)
      | ~ v1_orders_2(A_217)
      | ~ l1_orders_2(A_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1143])).

tff(c_1164,plain,(
    ! [A_220,A_219] :
      ( u1_struct_0(A_220) = u1_struct_0(A_219)
      | k3_lattice3(A_219) != A_220
      | ~ v1_orders_2(A_220)
      | ~ l1_orders_2(A_220)
      | ~ l3_lattices(A_219)
      | ~ v10_lattices(A_219)
      | v2_struct_0(A_219) ) ),
    inference(resolution,[status(thm)],[c_36,c_1159])).

tff(c_1168,plain,(
    ! [A_221,A_222] :
      ( u1_struct_0(k3_lattice3(A_221)) = u1_struct_0(A_222)
      | k3_lattice3(A_222) != k3_lattice3(A_221)
      | ~ l1_orders_2(k3_lattice3(A_221))
      | ~ l3_lattices(A_222)
      | ~ v10_lattices(A_222)
      | v2_struct_0(A_222)
      | ~ l3_lattices(A_221)
      | ~ v10_lattices(A_221)
      | v2_struct_0(A_221) ) ),
    inference(resolution,[status(thm)],[c_64,c_1164])).

tff(c_1177,plain,(
    ! [A_39,A_222] :
      ( u1_struct_0(k3_lattice3(A_39)) = u1_struct_0(A_222)
      | k3_lattice3(A_39) != k3_lattice3(A_222)
      | ~ l3_lattices(A_222)
      | ~ v10_lattices(A_222)
      | v2_struct_0(A_222)
      | ~ l3_lattices(A_39)
      | ~ v10_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_46,c_1168])).

tff(c_888,plain,(
    l1_orders_2(k3_lattice3('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_876])).

tff(c_1170,plain,(
    ! [A_222] :
      ( u1_struct_0(k3_lattice3('#skF_2')) = u1_struct_0(A_222)
      | k3_lattice3(A_222) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_222)
      | ~ v10_lattices(A_222)
      | v2_struct_0(A_222)
      | ~ l3_lattices('#skF_2')
      | ~ v10_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_888,c_1168])).

tff(c_1175,plain,(
    ! [A_222] :
      ( u1_struct_0(k3_lattice3('#skF_2')) = u1_struct_0(A_222)
      | k3_lattice3(A_222) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_222)
      | ~ v10_lattices(A_222)
      | v2_struct_0(A_222)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1170])).

tff(c_1178,plain,(
    ! [A_223] :
      ( u1_struct_0(k3_lattice3('#skF_2')) = u1_struct_0(A_223)
      | k3_lattice3(A_223) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_223)
      | ~ v10_lattices(A_223)
      | v2_struct_0(A_223) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1175])).

tff(c_1281,plain,(
    ! [A_223] :
      ( g1_orders_2(u1_struct_0(A_223),u1_orders_2(k3_lattice3('#skF_2'))) = k3_lattice3('#skF_2')
      | ~ v1_orders_2(k3_lattice3('#skF_2'))
      | ~ l1_orders_2(k3_lattice3('#skF_2'))
      | k3_lattice3(A_223) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_223)
      | ~ v10_lattices(A_223)
      | v2_struct_0(A_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1178,c_4])).

tff(c_1314,plain,(
    ! [A_223] :
      ( g1_orders_2(u1_struct_0(A_223),u1_orders_2(k3_lattice3('#skF_2'))) = k3_lattice3('#skF_2')
      | ~ v1_orders_2(k3_lattice3('#skF_2'))
      | k3_lattice3(A_223) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_223)
      | ~ v10_lattices(A_223)
      | v2_struct_0(A_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_1281])).

tff(c_2140,plain,(
    ~ v1_orders_2(k3_lattice3('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1314])).

tff(c_2143,plain,
    ( ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_2140])).

tff(c_2146,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_2143])).

tff(c_2148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2146])).

tff(c_2150,plain,(
    v1_orders_2(k3_lattice3('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1314])).

tff(c_172,plain,(
    ! [D_70,B_71,C_72,A_73] :
      ( D_70 = B_71
      | g1_orders_2(C_72,D_70) != g1_orders_2(A_73,B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_zfmisc_1(A_73,A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1148,plain,(
    ! [A_212,D_213,C_214] :
      ( k2_lattice3(A_212) = D_213
      | k3_lattice3(A_212) != g1_orders_2(C_214,D_213)
      | ~ m1_subset_1(k2_lattice3(A_212),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_212),u1_struct_0(A_212))))
      | ~ l3_lattices(A_212)
      | ~ v10_lattices(A_212)
      | v2_struct_0(A_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_172])).

tff(c_1152,plain,(
    ! [A_4,A_212] :
      ( u1_orders_2(A_4) = k2_lattice3(A_212)
      | k3_lattice3(A_212) != A_4
      | ~ m1_subset_1(k2_lattice3(A_212),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_212),u1_struct_0(A_212))))
      | ~ l3_lattices(A_212)
      | ~ v10_lattices(A_212)
      | v2_struct_0(A_212)
      | ~ v1_orders_2(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1148])).

tff(c_3835,plain,(
    ! [A_310] :
      ( u1_orders_2(k3_lattice3(A_310)) = k2_lattice3(A_310)
      | ~ m1_subset_1(k2_lattice3(A_310),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_310),u1_struct_0(A_310))))
      | ~ l3_lattices(A_310)
      | ~ v10_lattices(A_310)
      | v2_struct_0(A_310)
      | ~ v1_orders_2(k3_lattice3(A_310))
      | ~ l1_orders_2(k3_lattice3(A_310)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1152])).

tff(c_3887,plain,(
    ! [A_311] :
      ( u1_orders_2(k3_lattice3(A_311)) = k2_lattice3(A_311)
      | ~ v1_orders_2(k3_lattice3(A_311))
      | ~ l1_orders_2(k3_lattice3(A_311))
      | ~ l3_lattices(A_311)
      | ~ v10_lattices(A_311)
      | v2_struct_0(A_311) ) ),
    inference(resolution,[status(thm)],[c_36,c_3835])).

tff(c_3890,plain,
    ( u1_orders_2(k3_lattice3('#skF_2')) = k2_lattice3('#skF_2')
    | ~ l1_orders_2(k3_lattice3('#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2150,c_3887])).

tff(c_3896,plain,
    ( u1_orders_2(k3_lattice3('#skF_2')) = k2_lattice3('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_888,c_3890])).

tff(c_3897,plain,(
    u1_orders_2(k3_lattice3('#skF_2')) = k2_lattice3('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3896])).

tff(c_3921,plain,
    ( g1_orders_2(u1_struct_0(k3_lattice3('#skF_2')),k2_lattice3('#skF_2')) = k3_lattice3('#skF_2')
    | ~ v1_orders_2(k3_lattice3('#skF_2'))
    | ~ l1_orders_2(k3_lattice3('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3897,c_4])).

tff(c_3932,plain,(
    g1_orders_2(u1_struct_0(k3_lattice3('#skF_2')),k2_lattice3('#skF_2')) = k3_lattice3('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_2150,c_3921])).

tff(c_4098,plain,(
    ! [A_222] :
      ( g1_orders_2(u1_struct_0(A_222),k2_lattice3('#skF_2')) = k3_lattice3('#skF_2')
      | k3_lattice3(A_222) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_222)
      | ~ v10_lattices(A_222)
      | v2_struct_0(A_222)
      | ~ l3_lattices('#skF_2')
      | ~ v10_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1177,c_3932])).

tff(c_4148,plain,(
    ! [A_222] :
      ( g1_orders_2(u1_struct_0(A_222),k2_lattice3('#skF_2')) = k3_lattice3('#skF_2')
      | k3_lattice3(A_222) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_222)
      | ~ v10_lattices(A_222)
      | v2_struct_0(A_222)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_4098])).

tff(c_4150,plain,(
    ! [A_314] :
      ( g1_orders_2(u1_struct_0(A_314),k2_lattice3('#skF_2')) = k3_lattice3('#skF_2')
      | k3_lattice3(A_314) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_314)
      | ~ v10_lattices(A_314)
      | v2_struct_0(A_314) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4148])).

tff(c_2186,plain,(
    ! [A_242] :
      ( g1_orders_2(u1_struct_0(A_242),u1_orders_2(k3_lattice3('#skF_2'))) = k3_lattice3('#skF_2')
      | k3_lattice3(A_242) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_242)
      | ~ v10_lattices(A_242)
      | v2_struct_0(A_242) ) ),
    inference(splitRight,[status(thm)],[c_1314])).

tff(c_10,plain,(
    ! [D_17,B_13,C_16,A_12] :
      ( D_17 = B_13
      | g1_orders_2(C_16,D_17) != g1_orders_2(A_12,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k2_zfmisc_1(A_12,A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2215,plain,(
    ! [B_13,A_12,A_242] :
      ( u1_orders_2(k3_lattice3('#skF_2')) = B_13
      | g1_orders_2(A_12,B_13) != k3_lattice3('#skF_2')
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k2_zfmisc_1(A_12,A_12)))
      | k3_lattice3(A_242) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_242)
      | ~ v10_lattices(A_242)
      | v2_struct_0(A_242) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2186,c_10])).

tff(c_2834,plain,(
    ! [A_276] :
      ( k3_lattice3(A_276) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_276)
      | ~ v10_lattices(A_276)
      | v2_struct_0(A_276) ) ),
    inference(splitLeft,[status(thm)],[c_2215])).

tff(c_2843,plain,
    ( ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_2834,c_78])).

tff(c_2849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_2843])).

tff(c_2851,plain,(
    ! [B_277,A_278] :
      ( u1_orders_2(k3_lattice3('#skF_2')) = B_277
      | g1_orders_2(A_278,B_277) != k3_lattice3('#skF_2')
      | ~ m1_subset_1(B_277,k1_zfmisc_1(k2_zfmisc_1(A_278,A_278))) ) ),
    inference(splitRight,[status(thm)],[c_2215])).

tff(c_2875,plain,(
    ! [A_282] :
      ( u1_orders_2(k3_lattice3('#skF_2')) = k2_lattice3(A_282)
      | g1_orders_2(u1_struct_0(A_282),k2_lattice3(A_282)) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_282)
      | ~ v10_lattices(A_282)
      | v2_struct_0(A_282) ) ),
    inference(resolution,[status(thm)],[c_36,c_2851])).

tff(c_2913,plain,(
    ! [A_283] :
      ( u1_orders_2(k3_lattice3('#skF_2')) = k2_lattice3(A_283)
      | k3_lattice3(A_283) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_283)
      | ~ v10_lattices(A_283)
      | v2_struct_0(A_283)
      | ~ l3_lattices(A_283)
      | ~ v10_lattices(A_283)
      | v2_struct_0(A_283) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2875])).

tff(c_2954,plain,(
    ! [A_283] :
      ( g1_orders_2(u1_struct_0(k3_lattice3('#skF_2')),k2_lattice3(A_283)) = k3_lattice3('#skF_2')
      | ~ v1_orders_2(k3_lattice3('#skF_2'))
      | ~ l1_orders_2(k3_lattice3('#skF_2'))
      | k3_lattice3(A_283) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_283)
      | ~ v10_lattices(A_283)
      | v2_struct_0(A_283)
      | ~ l3_lattices(A_283)
      | ~ v10_lattices(A_283)
      | v2_struct_0(A_283) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2913,c_4])).

tff(c_3087,plain,(
    ! [A_287] :
      ( g1_orders_2(u1_struct_0(k3_lattice3('#skF_2')),k2_lattice3(A_287)) = k3_lattice3('#skF_2')
      | k3_lattice3(A_287) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_287)
      | ~ v10_lattices(A_287)
      | v2_struct_0(A_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_2150,c_2954])).

tff(c_12,plain,(
    ! [C_16,A_12,D_17,B_13] :
      ( C_16 = A_12
      | g1_orders_2(C_16,D_17) != g1_orders_2(A_12,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k2_zfmisc_1(A_12,A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3115,plain,(
    ! [A_12,B_13,A_287] :
      ( u1_struct_0(k3_lattice3('#skF_2')) = A_12
      | g1_orders_2(A_12,B_13) != k3_lattice3('#skF_2')
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k2_zfmisc_1(A_12,A_12)))
      | k3_lattice3(A_287) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_287)
      | ~ v10_lattices(A_287)
      | v2_struct_0(A_287) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3087,c_12])).

tff(c_3664,plain,(
    ! [A_304] :
      ( k3_lattice3(A_304) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_304)
      | ~ v10_lattices(A_304)
      | v2_struct_0(A_304) ) ),
    inference(splitLeft,[status(thm)],[c_3115])).

tff(c_3673,plain,
    ( ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_3664,c_78])).

tff(c_3679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_3673])).

tff(c_3681,plain,(
    ! [A_305,B_306] :
      ( u1_struct_0(k3_lattice3('#skF_2')) = A_305
      | g1_orders_2(A_305,B_306) != k3_lattice3('#skF_2')
      | ~ m1_subset_1(B_306,k1_zfmisc_1(k2_zfmisc_1(A_305,A_305))) ) ),
    inference(splitRight,[status(thm)],[c_3115])).

tff(c_3685,plain,(
    ! [A_38] :
      ( u1_struct_0(k3_lattice3('#skF_2')) = u1_struct_0(A_38)
      | g1_orders_2(u1_struct_0(A_38),k2_lattice3(A_38)) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_38)
      | ~ v10_lattices(A_38)
      | v2_struct_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_36,c_3681])).

tff(c_4172,plain,
    ( u1_struct_0(k3_lattice3('#skF_2')) = u1_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4150,c_3685])).

tff(c_4268,plain,
    ( u1_struct_0(k3_lattice3('#skF_2')) = u1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_4172])).

tff(c_4269,plain,(
    u1_struct_0(k3_lattice3('#skF_2')) = u1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4268])).

tff(c_8,plain,(
    ! [B_9,C_11,A_5] :
      ( r2_hidden(k4_tarski(B_9,C_11),u1_orders_2(A_5))
      | ~ r1_orders_2(A_5,B_9,C_11)
      | ~ m1_subset_1(C_11,u1_struct_0(A_5))
      | ~ m1_subset_1(B_9,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3918,plain,(
    ! [B_9,C_11] :
      ( r2_hidden(k4_tarski(B_9,C_11),k2_lattice3('#skF_2'))
      | ~ r1_orders_2(k3_lattice3('#skF_2'),B_9,C_11)
      | ~ m1_subset_1(C_11,u1_struct_0(k3_lattice3('#skF_2')))
      | ~ m1_subset_1(B_9,u1_struct_0(k3_lattice3('#skF_2')))
      | ~ l1_orders_2(k3_lattice3('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3897,c_8])).

tff(c_3930,plain,(
    ! [B_9,C_11] :
      ( r2_hidden(k4_tarski(B_9,C_11),k2_lattice3('#skF_2'))
      | ~ r1_orders_2(k3_lattice3('#skF_2'),B_9,C_11)
      | ~ m1_subset_1(C_11,u1_struct_0(k3_lattice3('#skF_2')))
      | ~ m1_subset_1(B_9,u1_struct_0(k3_lattice3('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_3918])).

tff(c_6692,plain,(
    ! [B_369,C_370] :
      ( r2_hidden(k4_tarski(B_369,C_370),k2_lattice3('#skF_2'))
      | ~ r1_orders_2(k3_lattice3('#skF_2'),B_369,C_370)
      | ~ m1_subset_1(C_370,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_369,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4269,c_4269,c_3930])).

tff(c_249,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k1_domain_1(A_88,B_89,C_90,D_91) = k4_tarski(C_90,D_91)
      | ~ m1_subset_1(D_91,B_89)
      | ~ m1_subset_1(C_90,A_88)
      | v1_xboole_0(B_89)
      | v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_269,plain,(
    ! [A_88,C_90] :
      ( k1_domain_1(A_88,u1_struct_0('#skF_2'),C_90,'#skF_4') = k4_tarski(C_90,'#skF_4')
      | ~ m1_subset_1(C_90,A_88)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_70,c_249])).

tff(c_271,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_128,plain,(
    ! [A_65] :
      ( m1_subset_1('#skF_1'(A_65),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l3_lattices(A_65)
      | ~ v10_lattices(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_xboole_0(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_132,plain,(
    ! [A_65] :
      ( v1_xboole_0('#skF_1'(A_65))
      | ~ v1_xboole_0(u1_struct_0(A_65))
      | ~ l3_lattices(A_65)
      | ~ v10_lattices(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_274,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_271,c_132])).

tff(c_277,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_274])).

tff(c_278,plain,(
    v1_xboole_0('#skF_1'('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_277])).

tff(c_24,plain,(
    ! [A_25] :
      ( ~ v1_xboole_0('#skF_1'(A_25))
      | ~ l3_lattices(A_25)
      | ~ v10_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_281,plain,
    ( ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_278,c_24])).

tff(c_284,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_281])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_284])).

tff(c_288,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_112,plain,(
    ! [A_63] :
      ( k8_filter_1(A_63) = k2_lattice3(A_63)
      | ~ l3_lattices(A_63)
      | ~ v10_lattices(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_118,plain,
    ( k8_filter_1('#skF_2') = k2_lattice3('#skF_2')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_112,c_78])).

tff(c_122,plain,(
    k8_filter_1('#skF_2') = k2_lattice3('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_118])).

tff(c_287,plain,(
    ! [A_88,C_90] :
      ( k1_domain_1(A_88,u1_struct_0('#skF_2'),C_90,'#skF_4') = k4_tarski(C_90,'#skF_4')
      | ~ m1_subset_1(C_90,A_88)
      | v1_xboole_0(A_88) ) ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_939,plain,(
    ! [A_188,B_189,C_190] :
      ( r3_lattices(A_188,B_189,C_190)
      | ~ r2_hidden(k1_domain_1(u1_struct_0(A_188),u1_struct_0(A_188),B_189,C_190),k8_filter_1(A_188))
      | ~ m1_subset_1(C_190,u1_struct_0(A_188))
      | ~ m1_subset_1(B_189,u1_struct_0(A_188))
      | ~ l3_lattices(A_188)
      | ~ v10_lattices(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_955,plain,(
    ! [C_90] :
      ( r3_lattices('#skF_2',C_90,'#skF_4')
      | ~ r2_hidden(k4_tarski(C_90,'#skF_4'),k8_filter_1('#skF_2'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_90,u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v10_lattices('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_90,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_939])).

tff(c_969,plain,(
    ! [C_90] :
      ( r3_lattices('#skF_2',C_90,'#skF_4')
      | ~ r2_hidden(k4_tarski(C_90,'#skF_4'),k2_lattice3('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_90,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_122,c_955])).

tff(c_970,plain,(
    ! [C_90] :
      ( r3_lattices('#skF_2',C_90,'#skF_4')
      | ~ r2_hidden(k4_tarski(C_90,'#skF_4'),k2_lattice3('#skF_2'))
      | ~ m1_subset_1(C_90,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_78,c_969])).

tff(c_6703,plain,(
    ! [B_369] :
      ( r3_lattices('#skF_2',B_369,'#skF_4')
      | ~ r1_orders_2(k3_lattice3('#skF_2'),B_369,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_369,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_6692,c_970])).

tff(c_6743,plain,(
    ! [B_374] :
      ( r3_lattices('#skF_2',B_374,'#skF_4')
      | ~ r1_orders_2(k3_lattice3('#skF_2'),B_374,'#skF_4')
      | ~ m1_subset_1(B_374,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6703])).

tff(c_6749,plain,
    ( r3_lattices('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_922,c_6743])).

tff(c_6753,plain,(
    r3_lattices('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6749])).

tff(c_6755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_6753])).

tff(c_6756,plain,(
    r3_lattices('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_6883,plain,(
    ! [A_404,B_405,C_406,D_407] :
      ( k1_domain_1(A_404,B_405,C_406,D_407) = k4_tarski(C_406,D_407)
      | ~ m1_subset_1(D_407,B_405)
      | ~ m1_subset_1(C_406,A_404)
      | v1_xboole_0(B_405)
      | v1_xboole_0(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6897,plain,(
    ! [A_404,C_406] :
      ( k1_domain_1(A_404,u1_struct_0('#skF_2'),C_406,'#skF_4') = k4_tarski(C_406,'#skF_4')
      | ~ m1_subset_1(C_406,A_404)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(A_404) ) ),
    inference(resolution,[status(thm)],[c_70,c_6883])).

tff(c_6914,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6897])).

tff(c_6794,plain,(
    ! [A_387] :
      ( m1_subset_1('#skF_1'(A_387),k1_zfmisc_1(u1_struct_0(A_387)))
      | ~ l3_lattices(A_387)
      | ~ v10_lattices(A_387)
      | v2_struct_0(A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6798,plain,(
    ! [A_387] :
      ( v1_xboole_0('#skF_1'(A_387))
      | ~ v1_xboole_0(u1_struct_0(A_387))
      | ~ l3_lattices(A_387)
      | ~ v10_lattices(A_387)
      | v2_struct_0(A_387) ) ),
    inference(resolution,[status(thm)],[c_6794,c_2])).

tff(c_6917,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6914,c_6798])).

tff(c_6920,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_6917])).

tff(c_6921,plain,(
    v1_xboole_0('#skF_1'('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6920])).

tff(c_6924,plain,
    ( ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6921,c_24])).

tff(c_6927,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_6924])).

tff(c_6929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6927])).

tff(c_6931,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_6897])).

tff(c_6778,plain,(
    ! [A_385] :
      ( k8_filter_1(A_385) = k2_lattice3(A_385)
      | ~ l3_lattices(A_385)
      | ~ v10_lattices(A_385)
      | v2_struct_0(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_6784,plain,
    ( k8_filter_1('#skF_2') = k2_lattice3('#skF_2')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_6778,c_78])).

tff(c_6788,plain,(
    k8_filter_1('#skF_2') = k2_lattice3('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_6784])).

tff(c_6930,plain,(
    ! [A_404,C_406] :
      ( k1_domain_1(A_404,u1_struct_0('#skF_2'),C_406,'#skF_4') = k4_tarski(C_406,'#skF_4')
      | ~ m1_subset_1(C_406,A_404)
      | v1_xboole_0(A_404) ) ),
    inference(splitRight,[status(thm)],[c_6897])).

tff(c_7771,plain,(
    ! [A_540,B_541,C_542] :
      ( r2_hidden(k1_domain_1(u1_struct_0(A_540),u1_struct_0(A_540),B_541,C_542),k8_filter_1(A_540))
      | ~ r3_lattices(A_540,B_541,C_542)
      | ~ m1_subset_1(C_542,u1_struct_0(A_540))
      | ~ m1_subset_1(B_541,u1_struct_0(A_540))
      | ~ l3_lattices(A_540)
      | ~ v10_lattices(A_540)
      | v2_struct_0(A_540) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_7790,plain,(
    ! [C_406] :
      ( r2_hidden(k4_tarski(C_406,'#skF_4'),k8_filter_1('#skF_2'))
      | ~ r3_lattices('#skF_2',C_406,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_406,u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v10_lattices('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_406,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6930,c_7771])).

tff(c_7805,plain,(
    ! [C_406] :
      ( r2_hidden(k4_tarski(C_406,'#skF_4'),k2_lattice3('#skF_2'))
      | ~ r3_lattices('#skF_2',C_406,'#skF_4')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_406,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_6788,c_7790])).

tff(c_7806,plain,(
    ! [C_406] :
      ( r2_hidden(k4_tarski(C_406,'#skF_4'),k2_lattice3('#skF_2'))
      | ~ r3_lattices('#skF_2',C_406,'#skF_4')
      | ~ m1_subset_1(C_406,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6931,c_78,c_7805])).

tff(c_6835,plain,(
    ! [A_398,B_399] :
      ( k4_lattice3(A_398,B_399) = B_399
      | ~ m1_subset_1(B_399,u1_struct_0(A_398))
      | ~ l3_lattices(A_398)
      | ~ v10_lattices(A_398)
      | v2_struct_0(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_6841,plain,
    ( k4_lattice3('#skF_2','#skF_3') = '#skF_3'
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_6835])).

tff(c_6848,plain,
    ( k4_lattice3('#skF_2','#skF_3') = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_6841])).

tff(c_6849,plain,(
    k4_lattice3('#skF_2','#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6848])).

tff(c_6866,plain,(
    ! [A_402,B_403] :
      ( m1_subset_1(k4_lattice3(A_402,B_403),u1_struct_0(k3_lattice3(A_402)))
      | ~ m1_subset_1(B_403,u1_struct_0(A_402))
      | ~ l3_lattices(A_402)
      | ~ v10_lattices(A_402)
      | v2_struct_0(A_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_6872,plain,
    ( m1_subset_1('#skF_3',u1_struct_0(k3_lattice3('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6849,c_6866])).

tff(c_6878,plain,
    ( m1_subset_1('#skF_3',u1_struct_0(k3_lattice3('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_6872])).

tff(c_6879,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k3_lattice3('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6878])).

tff(c_7607,plain,(
    ! [A_511,B_512,C_513] :
      ( r3_orders_2(A_511,B_512,C_513)
      | ~ r1_orders_2(A_511,B_512,C_513)
      | ~ m1_subset_1(C_513,u1_struct_0(A_511))
      | ~ m1_subset_1(B_512,u1_struct_0(A_511))
      | ~ l1_orders_2(A_511)
      | ~ v3_orders_2(A_511)
      | v2_struct_0(A_511) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_7619,plain,(
    ! [B_512] :
      ( r3_orders_2(k3_lattice3('#skF_2'),B_512,'#skF_3')
      | ~ r1_orders_2(k3_lattice3('#skF_2'),B_512,'#skF_3')
      | ~ m1_subset_1(B_512,u1_struct_0(k3_lattice3('#skF_2')))
      | ~ l1_orders_2(k3_lattice3('#skF_2'))
      | ~ v3_orders_2(k3_lattice3('#skF_2'))
      | v2_struct_0(k3_lattice3('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_6879,c_7607])).

tff(c_7664,plain,(
    ~ v3_orders_2(k3_lattice3('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7619])).

tff(c_7667,plain,
    ( ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_7664])).

tff(c_7670,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_7667])).

tff(c_7672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_7670])).

tff(c_7673,plain,(
    ! [B_512] :
      ( ~ l1_orders_2(k3_lattice3('#skF_2'))
      | v2_struct_0(k3_lattice3('#skF_2'))
      | r3_orders_2(k3_lattice3('#skF_2'),B_512,'#skF_3')
      | ~ r1_orders_2(k3_lattice3('#skF_2'),B_512,'#skF_3')
      | ~ m1_subset_1(B_512,u1_struct_0(k3_lattice3('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_7619])).

tff(c_7675,plain,(
    ~ l1_orders_2(k3_lattice3('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7673])).

tff(c_7678,plain,
    ( ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_7675])).

tff(c_7681,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_7678])).

tff(c_7683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_7681])).

tff(c_7685,plain,(
    l1_orders_2(k3_lattice3('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_7673])).

tff(c_6813,plain,(
    ! [C_390,A_391,D_392,B_393] :
      ( C_390 = A_391
      | g1_orders_2(C_390,D_392) != g1_orders_2(A_391,B_393)
      | ~ m1_subset_1(B_393,k1_zfmisc_1(k2_zfmisc_1(A_391,A_391))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7872,plain,(
    ! [A_550,C_551,D_552] :
      ( u1_struct_0(A_550) = C_551
      | k3_lattice3(A_550) != g1_orders_2(C_551,D_552)
      | ~ m1_subset_1(k2_lattice3(A_550),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_550),u1_struct_0(A_550))))
      | ~ l3_lattices(A_550)
      | ~ v10_lattices(A_550)
      | v2_struct_0(A_550) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_6813])).

tff(c_7940,plain,(
    ! [A_565,A_564] :
      ( u1_struct_0(A_565) = u1_struct_0(A_564)
      | k3_lattice3(A_564) != A_565
      | ~ m1_subset_1(k2_lattice3(A_564),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_564),u1_struct_0(A_564))))
      | ~ l3_lattices(A_564)
      | ~ v10_lattices(A_564)
      | v2_struct_0(A_564)
      | ~ v1_orders_2(A_565)
      | ~ l1_orders_2(A_565) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7872])).

tff(c_7975,plain,(
    ! [A_569,A_568] :
      ( u1_struct_0(A_569) = u1_struct_0(A_568)
      | k3_lattice3(A_569) != A_568
      | ~ v1_orders_2(A_568)
      | ~ l1_orders_2(A_568)
      | ~ l3_lattices(A_569)
      | ~ v10_lattices(A_569)
      | v2_struct_0(A_569) ) ),
    inference(resolution,[status(thm)],[c_36,c_7940])).

tff(c_7979,plain,(
    ! [A_570,A_571] :
      ( u1_struct_0(k3_lattice3(A_570)) = u1_struct_0(A_571)
      | k3_lattice3(A_571) != k3_lattice3(A_570)
      | ~ l1_orders_2(k3_lattice3(A_570))
      | ~ l3_lattices(A_571)
      | ~ v10_lattices(A_571)
      | v2_struct_0(A_571)
      | ~ l3_lattices(A_570)
      | ~ v10_lattices(A_570)
      | v2_struct_0(A_570) ) ),
    inference(resolution,[status(thm)],[c_64,c_7975])).

tff(c_7988,plain,(
    ! [A_39,A_571] :
      ( u1_struct_0(k3_lattice3(A_39)) = u1_struct_0(A_571)
      | k3_lattice3(A_571) != k3_lattice3(A_39)
      | ~ l3_lattices(A_571)
      | ~ v10_lattices(A_571)
      | v2_struct_0(A_571)
      | ~ l3_lattices(A_39)
      | ~ v10_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_46,c_7979])).

tff(c_7981,plain,(
    ! [A_571] :
      ( u1_struct_0(k3_lattice3('#skF_2')) = u1_struct_0(A_571)
      | k3_lattice3(A_571) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_571)
      | ~ v10_lattices(A_571)
      | v2_struct_0(A_571)
      | ~ l3_lattices('#skF_2')
      | ~ v10_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_7685,c_7979])).

tff(c_7986,plain,(
    ! [A_571] :
      ( u1_struct_0(k3_lattice3('#skF_2')) = u1_struct_0(A_571)
      | k3_lattice3(A_571) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_571)
      | ~ v10_lattices(A_571)
      | v2_struct_0(A_571)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_7981])).

tff(c_7989,plain,(
    ! [A_572] :
      ( u1_struct_0(k3_lattice3('#skF_2')) = u1_struct_0(A_572)
      | k3_lattice3(A_572) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_572)
      | ~ v10_lattices(A_572)
      | v2_struct_0(A_572) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_7986])).

tff(c_8098,plain,(
    ! [A_572] :
      ( g1_orders_2(u1_struct_0(A_572),u1_orders_2(k3_lattice3('#skF_2'))) = k3_lattice3('#skF_2')
      | ~ v1_orders_2(k3_lattice3('#skF_2'))
      | ~ l1_orders_2(k3_lattice3('#skF_2'))
      | k3_lattice3(A_572) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_572)
      | ~ v10_lattices(A_572)
      | v2_struct_0(A_572) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7989,c_4])).

tff(c_8132,plain,(
    ! [A_572] :
      ( g1_orders_2(u1_struct_0(A_572),u1_orders_2(k3_lattice3('#skF_2'))) = k3_lattice3('#skF_2')
      | ~ v1_orders_2(k3_lattice3('#skF_2'))
      | k3_lattice3(A_572) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_572)
      | ~ v10_lattices(A_572)
      | v2_struct_0(A_572) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7685,c_8098])).

tff(c_8987,plain,(
    ~ v1_orders_2(k3_lattice3('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_8132])).

tff(c_8990,plain,
    ( ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_8987])).

tff(c_8993,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_8990])).

tff(c_8995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8993])).

tff(c_8997,plain,(
    v1_orders_2(k3_lattice3('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_8132])).

tff(c_9054,plain,(
    ! [A_593] :
      ( g1_orders_2(u1_struct_0(A_593),u1_orders_2(k3_lattice3('#skF_2'))) = k3_lattice3('#skF_2')
      | k3_lattice3(A_593) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_593)
      | ~ v10_lattices(A_593)
      | v2_struct_0(A_593) ) ),
    inference(splitRight,[status(thm)],[c_8132])).

tff(c_9079,plain,(
    ! [B_13,A_12,A_593] :
      ( u1_orders_2(k3_lattice3('#skF_2')) = B_13
      | g1_orders_2(A_12,B_13) != k3_lattice3('#skF_2')
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k2_zfmisc_1(A_12,A_12)))
      | k3_lattice3(A_593) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_593)
      | ~ v10_lattices(A_593)
      | v2_struct_0(A_593) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9054,c_10])).

tff(c_9620,plain,(
    ! [A_623] :
      ( k3_lattice3(A_623) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_623)
      | ~ v10_lattices(A_623)
      | v2_struct_0(A_623) ) ),
    inference(splitLeft,[status(thm)],[c_9079])).

tff(c_9629,plain,
    ( ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_9620,c_78])).

tff(c_9635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_9629])).

tff(c_9637,plain,(
    ! [B_624,A_625] :
      ( u1_orders_2(k3_lattice3('#skF_2')) = B_624
      | g1_orders_2(A_625,B_624) != k3_lattice3('#skF_2')
      | ~ m1_subset_1(B_624,k1_zfmisc_1(k2_zfmisc_1(A_625,A_625))) ) ),
    inference(splitRight,[status(thm)],[c_9079])).

tff(c_9642,plain,(
    ! [A_626] :
      ( u1_orders_2(k3_lattice3('#skF_2')) = k2_lattice3(A_626)
      | g1_orders_2(u1_struct_0(A_626),k2_lattice3(A_626)) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_626)
      | ~ v10_lattices(A_626)
      | v2_struct_0(A_626) ) ),
    inference(resolution,[status(thm)],[c_36,c_9637])).

tff(c_9680,plain,(
    ! [A_627] :
      ( u1_orders_2(k3_lattice3('#skF_2')) = k2_lattice3(A_627)
      | k3_lattice3(A_627) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_627)
      | ~ v10_lattices(A_627)
      | v2_struct_0(A_627)
      | ~ l3_lattices(A_627)
      | ~ v10_lattices(A_627)
      | v2_struct_0(A_627) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_9642])).

tff(c_9721,plain,(
    ! [A_627] :
      ( g1_orders_2(u1_struct_0(k3_lattice3('#skF_2')),k2_lattice3(A_627)) = k3_lattice3('#skF_2')
      | ~ v1_orders_2(k3_lattice3('#skF_2'))
      | ~ l1_orders_2(k3_lattice3('#skF_2'))
      | k3_lattice3(A_627) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_627)
      | ~ v10_lattices(A_627)
      | v2_struct_0(A_627)
      | ~ l3_lattices(A_627)
      | ~ v10_lattices(A_627)
      | v2_struct_0(A_627) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9680,c_4])).

tff(c_9854,plain,(
    ! [A_631] :
      ( g1_orders_2(u1_struct_0(k3_lattice3('#skF_2')),k2_lattice3(A_631)) = k3_lattice3('#skF_2')
      | k3_lattice3(A_631) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_631)
      | ~ v10_lattices(A_631)
      | v2_struct_0(A_631) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7685,c_8997,c_9721])).

tff(c_9913,plain,(
    ! [A_571,A_631] :
      ( g1_orders_2(u1_struct_0(A_571),k2_lattice3(A_631)) = k3_lattice3('#skF_2')
      | k3_lattice3(A_631) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_631)
      | ~ v10_lattices(A_631)
      | v2_struct_0(A_631)
      | k3_lattice3(A_571) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_571)
      | ~ v10_lattices(A_571)
      | v2_struct_0(A_571)
      | ~ l3_lattices('#skF_2')
      | ~ v10_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7988,c_9854])).

tff(c_9928,plain,(
    ! [A_571,A_631] :
      ( g1_orders_2(u1_struct_0(A_571),k2_lattice3(A_631)) = k3_lattice3('#skF_2')
      | k3_lattice3(A_631) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_631)
      | ~ v10_lattices(A_631)
      | v2_struct_0(A_631)
      | k3_lattice3(A_571) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_571)
      | ~ v10_lattices(A_571)
      | v2_struct_0(A_571)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_9913])).

tff(c_9929,plain,(
    ! [A_571,A_631] :
      ( g1_orders_2(u1_struct_0(A_571),k2_lattice3(A_631)) = k3_lattice3('#skF_2')
      | k3_lattice3(A_631) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_631)
      | ~ v10_lattices(A_631)
      | v2_struct_0(A_631)
      | k3_lattice3(A_571) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_571)
      | ~ v10_lattices(A_571)
      | v2_struct_0(A_571) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_9928])).

tff(c_10777,plain,(
    ! [A_656,A_657] :
      ( g1_orders_2(u1_struct_0(A_656),k2_lattice3(A_657)) = k3_lattice3('#skF_2')
      | k3_lattice3(A_657) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_657)
      | ~ v10_lattices(A_657)
      | v2_struct_0(A_657)
      | k3_lattice3(A_656) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_656)
      | ~ v10_lattices(A_656)
      | v2_struct_0(A_656) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_9928])).

tff(c_6819,plain,(
    ! [A_4,A_391,B_393] :
      ( u1_struct_0(A_4) = A_391
      | g1_orders_2(A_391,B_393) != A_4
      | ~ m1_subset_1(B_393,k1_zfmisc_1(k2_zfmisc_1(A_391,A_391)))
      | ~ v1_orders_2(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_6813])).

tff(c_7592,plain,(
    ! [A_507,B_508] :
      ( u1_struct_0(g1_orders_2(A_507,B_508)) = A_507
      | ~ m1_subset_1(B_508,k1_zfmisc_1(k2_zfmisc_1(A_507,A_507)))
      | ~ v1_orders_2(g1_orders_2(A_507,B_508))
      | ~ l1_orders_2(g1_orders_2(A_507,B_508)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6819])).

tff(c_7596,plain,(
    ! [A_38] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(A_38),k2_lattice3(A_38))) = u1_struct_0(A_38)
      | ~ v1_orders_2(g1_orders_2(u1_struct_0(A_38),k2_lattice3(A_38)))
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(A_38),k2_lattice3(A_38)))
      | ~ l3_lattices(A_38)
      | ~ v10_lattices(A_38)
      | v2_struct_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_36,c_7592])).

tff(c_10784,plain,(
    ! [A_657] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(A_657),k2_lattice3(A_657))) = u1_struct_0(A_657)
      | ~ v1_orders_2(k3_lattice3('#skF_2'))
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(A_657),k2_lattice3(A_657)))
      | ~ l3_lattices(A_657)
      | ~ v10_lattices(A_657)
      | v2_struct_0(A_657)
      | k3_lattice3(A_657) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_657)
      | ~ v10_lattices(A_657)
      | v2_struct_0(A_657)
      | k3_lattice3(A_657) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_657)
      | ~ v10_lattices(A_657)
      | v2_struct_0(A_657) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10777,c_7596])).

tff(c_10909,plain,(
    ! [A_658] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(A_658),k2_lattice3(A_658))) = u1_struct_0(A_658)
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(A_658),k2_lattice3(A_658)))
      | k3_lattice3(A_658) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_658)
      | ~ v10_lattices(A_658)
      | v2_struct_0(A_658) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8997,c_10784])).

tff(c_10913,plain,(
    ! [A_631] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(A_631),k2_lattice3(A_631))) = u1_struct_0(A_631)
      | ~ l1_orders_2(k3_lattice3('#skF_2'))
      | k3_lattice3(A_631) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_631)
      | ~ v10_lattices(A_631)
      | v2_struct_0(A_631)
      | k3_lattice3(A_631) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_631)
      | ~ v10_lattices(A_631)
      | v2_struct_0(A_631)
      | k3_lattice3(A_631) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_631)
      | ~ v10_lattices(A_631)
      | v2_struct_0(A_631) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9929,c_10909])).

tff(c_10963,plain,(
    ! [A_659] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(A_659),k2_lattice3(A_659))) = u1_struct_0(A_659)
      | k3_lattice3(A_659) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_659)
      | ~ v10_lattices(A_659)
      | v2_struct_0(A_659) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7685,c_10913])).

tff(c_11165,plain,(
    ! [A_660] :
      ( u1_struct_0(k3_lattice3(A_660)) = u1_struct_0(A_660)
      | k3_lattice3(A_660) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_660)
      | ~ v10_lattices(A_660)
      | v2_struct_0(A_660)
      | ~ l3_lattices(A_660)
      | ~ v10_lattices(A_660)
      | v2_struct_0(A_660) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_10963])).

tff(c_8071,plain,(
    ! [A_572] :
      ( g1_orders_2(u1_struct_0(k3_lattice3('#skF_2')),k2_lattice3(A_572)) = k3_lattice3(A_572)
      | ~ l3_lattices(A_572)
      | ~ v10_lattices(A_572)
      | v2_struct_0(A_572)
      | k3_lattice3(A_572) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_572)
      | ~ v10_lattices(A_572)
      | v2_struct_0(A_572) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7989,c_32])).

tff(c_11210,plain,(
    ! [A_572] :
      ( g1_orders_2(u1_struct_0('#skF_2'),k2_lattice3(A_572)) = k3_lattice3(A_572)
      | k3_lattice3(A_572) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_572)
      | ~ v10_lattices(A_572)
      | v2_struct_0(A_572)
      | ~ l3_lattices('#skF_2')
      | ~ v10_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11165,c_8071])).

tff(c_11370,plain,(
    ! [A_572] :
      ( g1_orders_2(u1_struct_0('#skF_2'),k2_lattice3(A_572)) = k3_lattice3(A_572)
      | k3_lattice3(A_572) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_572)
      | ~ v10_lattices(A_572)
      | v2_struct_0(A_572)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_11210])).

tff(c_11467,plain,(
    ! [A_667] :
      ( g1_orders_2(u1_struct_0('#skF_2'),k2_lattice3(A_667)) = k3_lattice3(A_667)
      | k3_lattice3(A_667) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_667)
      | ~ v10_lattices(A_667)
      | v2_struct_0(A_667) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_11370])).

tff(c_10957,plain,(
    ! [A_631] :
      ( u1_struct_0(g1_orders_2(u1_struct_0(A_631),k2_lattice3(A_631))) = u1_struct_0(A_631)
      | k3_lattice3(A_631) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_631)
      | ~ v10_lattices(A_631)
      | v2_struct_0(A_631) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7685,c_10913])).

tff(c_11474,plain,
    ( u1_struct_0(k3_lattice3('#skF_2')) = u1_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11467,c_10957])).

tff(c_11572,plain,
    ( u1_struct_0(k3_lattice3('#skF_2')) = u1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_11474])).

tff(c_11573,plain,(
    u1_struct_0(k3_lattice3('#skF_2')) = u1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_11572])).

tff(c_9641,plain,(
    ! [A_38] :
      ( u1_orders_2(k3_lattice3('#skF_2')) = k2_lattice3(A_38)
      | g1_orders_2(u1_struct_0(A_38),k2_lattice3(A_38)) != k3_lattice3('#skF_2')
      | ~ l3_lattices(A_38)
      | ~ v10_lattices(A_38)
      | v2_struct_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_36,c_9637])).

tff(c_11514,plain,
    ( u1_orders_2(k3_lattice3('#skF_2')) = k2_lattice3('#skF_2')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11467,c_9641])).

tff(c_11597,plain,
    ( u1_orders_2(k3_lattice3('#skF_2')) = k2_lattice3('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_11514])).

tff(c_11598,plain,(
    u1_orders_2(k3_lattice3('#skF_2')) = k2_lattice3('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_11597])).

tff(c_6,plain,(
    ! [A_5,B_9,C_11] :
      ( r1_orders_2(A_5,B_9,C_11)
      | ~ r2_hidden(k4_tarski(B_9,C_11),u1_orders_2(A_5))
      | ~ m1_subset_1(C_11,u1_struct_0(A_5))
      | ~ m1_subset_1(B_9,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_11886,plain,(
    ! [B_9,C_11] :
      ( r1_orders_2(k3_lattice3('#skF_2'),B_9,C_11)
      | ~ r2_hidden(k4_tarski(B_9,C_11),k2_lattice3('#skF_2'))
      | ~ m1_subset_1(C_11,u1_struct_0(k3_lattice3('#skF_2')))
      | ~ m1_subset_1(B_9,u1_struct_0(k3_lattice3('#skF_2')))
      | ~ l1_orders_2(k3_lattice3('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11598,c_6])).

tff(c_13416,plain,(
    ! [B_698,C_699] :
      ( r1_orders_2(k3_lattice3('#skF_2'),B_698,C_699)
      | ~ r2_hidden(k4_tarski(B_698,C_699),k2_lattice3('#skF_2'))
      | ~ m1_subset_1(C_699,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_698,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7685,c_11573,c_11573,c_11886])).

tff(c_13421,plain,(
    ! [C_406] :
      ( r1_orders_2(k3_lattice3('#skF_2'),C_406,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ r3_lattices('#skF_2',C_406,'#skF_4')
      | ~ m1_subset_1(C_406,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_7806,c_13416])).

tff(c_13456,plain,(
    ! [C_703] :
      ( r1_orders_2(k3_lattice3('#skF_2'),C_703,'#skF_4')
      | ~ r3_lattices('#skF_2',C_703,'#skF_4')
      | ~ m1_subset_1(C_703,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_13421])).

tff(c_6838,plain,
    ( k4_lattice3('#skF_2','#skF_4') = '#skF_4'
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_6835])).

tff(c_6844,plain,
    ( k4_lattice3('#skF_2','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_6838])).

tff(c_6845,plain,(
    k4_lattice3('#skF_2','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6844])).

tff(c_6760,plain,(
    ~ r3_orders_2(k3_lattice3('#skF_2'),k4_lattice3('#skF_2','#skF_3'),k4_lattice3('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6756,c_80])).

tff(c_6850,plain,(
    ~ r3_orders_2(k3_lattice3('#skF_2'),k4_lattice3('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6845,c_6760])).

tff(c_6859,plain,(
    ~ r3_orders_2(k3_lattice3('#skF_2'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6849,c_6850])).

tff(c_7684,plain,(
    ! [B_512] :
      ( v2_struct_0(k3_lattice3('#skF_2'))
      | r3_orders_2(k3_lattice3('#skF_2'),B_512,'#skF_3')
      | ~ r1_orders_2(k3_lattice3('#skF_2'),B_512,'#skF_3')
      | ~ m1_subset_1(B_512,u1_struct_0(k3_lattice3('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_7673])).

tff(c_7723,plain,(
    v2_struct_0(k3_lattice3('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7684])).

tff(c_7741,plain,
    ( ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_7723,c_66])).

tff(c_7744,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_7741])).

tff(c_7746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_7744])).

tff(c_7748,plain,(
    ~ v2_struct_0(k3_lattice3('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_7684])).

tff(c_7674,plain,(
    v3_orders_2(k3_lattice3('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_7619])).

tff(c_6875,plain,
    ( m1_subset_1('#skF_4',u1_struct_0(k3_lattice3('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6845,c_6866])).

tff(c_6881,plain,
    ( m1_subset_1('#skF_4',u1_struct_0(k3_lattice3('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_6875])).

tff(c_6882,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k3_lattice3('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6881])).

tff(c_7618,plain,(
    ! [B_512] :
      ( r3_orders_2(k3_lattice3('#skF_2'),B_512,'#skF_4')
      | ~ r1_orders_2(k3_lattice3('#skF_2'),B_512,'#skF_4')
      | ~ m1_subset_1(B_512,u1_struct_0(k3_lattice3('#skF_2')))
      | ~ l1_orders_2(k3_lattice3('#skF_2'))
      | ~ v3_orders_2(k3_lattice3('#skF_2'))
      | v2_struct_0(k3_lattice3('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_6882,c_7607])).

tff(c_7878,plain,(
    ! [B_512] :
      ( r3_orders_2(k3_lattice3('#skF_2'),B_512,'#skF_4')
      | ~ r1_orders_2(k3_lattice3('#skF_2'),B_512,'#skF_4')
      | ~ m1_subset_1(B_512,u1_struct_0(k3_lattice3('#skF_2')))
      | v2_struct_0(k3_lattice3('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7674,c_7685,c_7618])).

tff(c_7880,plain,(
    ! [B_553] :
      ( r3_orders_2(k3_lattice3('#skF_2'),B_553,'#skF_4')
      | ~ r1_orders_2(k3_lattice3('#skF_2'),B_553,'#skF_4')
      | ~ m1_subset_1(B_553,u1_struct_0(k3_lattice3('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_7748,c_7878])).

tff(c_7886,plain,
    ( r3_orders_2(k3_lattice3('#skF_2'),'#skF_3','#skF_4')
    | ~ r1_orders_2(k3_lattice3('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_6879,c_7880])).

tff(c_7894,plain,(
    ~ r1_orders_2(k3_lattice3('#skF_2'),'#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_6859,c_7886])).

tff(c_13462,plain,
    ( ~ r3_lattices('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_13456,c_7894])).

tff(c_13469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6756,c_13462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:34:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.64/3.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.71/3.88  
% 10.71/3.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.71/3.89  %$ r3_orders_2 > r3_lattices > r1_orders_2 > v1_partfun1 > v19_lattices > v18_lattices > r2_hidden > m1_subset_1 > v8_relat_2 > v5_orders_2 > v4_relat_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_2 > v1_orders_2 > v10_lattices > l3_lattices > l1_orders_2 > k1_domain_1 > k4_tarski > k4_lattice3 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k8_filter_1 > k3_lattice3 > k2_lattice3 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 10.71/3.89  
% 10.71/3.89  %Foreground sorts:
% 10.71/3.89  
% 10.71/3.89  
% 10.71/3.89  %Background operators:
% 10.71/3.89  
% 10.71/3.89  
% 10.71/3.89  %Foreground operators:
% 10.71/3.89  tff(l3_lattices, type, l3_lattices: $i > $o).
% 10.71/3.89  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 10.71/3.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.71/3.89  tff(k1_domain_1, type, k1_domain_1: ($i * $i * $i * $i) > $i).
% 10.71/3.89  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 10.71/3.89  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 10.71/3.89  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 10.71/3.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.71/3.89  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 10.71/3.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.71/3.89  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.71/3.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.71/3.89  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 10.71/3.89  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 10.71/3.89  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 10.71/3.89  tff(k4_lattice3, type, k4_lattice3: ($i * $i) > $i).
% 10.71/3.89  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 10.71/3.89  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 10.71/3.89  tff('#skF_2', type, '#skF_2': $i).
% 10.71/3.89  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.71/3.89  tff('#skF_3', type, '#skF_3': $i).
% 10.71/3.89  tff(v19_lattices, type, v19_lattices: ($i * $i) > $o).
% 10.71/3.89  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 10.71/3.89  tff(v18_lattices, type, v18_lattices: ($i * $i) > $o).
% 10.71/3.89  tff(v10_lattices, type, v10_lattices: $i > $o).
% 10.71/3.89  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 10.71/3.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.71/3.89  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 10.71/3.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.71/3.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.71/3.89  tff('#skF_4', type, '#skF_4': $i).
% 10.71/3.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.71/3.89  tff(k8_filter_1, type, k8_filter_1: $i > $i).
% 10.71/3.89  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 10.71/3.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.71/3.89  tff(k2_lattice3, type, k2_lattice3: $i > $i).
% 10.71/3.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.71/3.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.71/3.89  
% 10.97/3.93  tff(f_231, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_lattices(A, B, C) <=> r3_orders_2(k3_lattice3(A), k4_lattice3(A, B), k4_lattice3(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_lattice3)).
% 10.97/3.93  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => ((((v1_orders_2(k3_lattice3(A)) & v3_orders_2(k3_lattice3(A))) & v4_orders_2(k3_lattice3(A))) & v5_orders_2(k3_lattice3(A))) & l1_orders_2(k3_lattice3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_lattice3)).
% 10.97/3.93  tff(f_204, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => ((((~v2_struct_0(k3_lattice3(A)) & v1_orders_2(k3_lattice3(A))) & v3_orders_2(k3_lattice3(A))) & v4_orders_2(k3_lattice3(A))) & v5_orders_2(k3_lattice3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_lattice3)).
% 10.97/3.93  tff(f_141, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattice3(A, B) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattice3)).
% 10.97/3.93  tff(f_186, axiom, (![A, B]: ((((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k4_lattice3(A, B), u1_struct_0(k3_lattice3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_lattice3)).
% 10.97/3.93  tff(f_86, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 10.97/3.93  tff(f_158, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => ((((v1_partfun1(k2_lattice3(A), u1_struct_0(A)) & v1_relat_2(k2_lattice3(A))) & v4_relat_2(k2_lattice3(A))) & v8_relat_2(k2_lattice3(A))) & m1_subset_1(k2_lattice3(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_lattice3)).
% 10.97/3.93  tff(f_38, axiom, (![A]: (l1_orders_2(A) => (v1_orders_2(A) => (A = g1_orders_2(u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 10.97/3.93  tff(f_129, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (k3_lattice3(A) = g1_orders_2(u1_struct_0(A), k2_lattice3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_lattice3)).
% 10.97/3.93  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 10.97/3.93  tff(f_50, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 10.97/3.93  tff(f_71, axiom, (![A, B, C, D]: ((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & m1_subset_1(C, A)) & m1_subset_1(D, B)) => (k1_domain_1(A, B, C, D) = k4_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_domain_1)).
% 10.97/3.93  tff(f_103, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v18_lattices(B, A)) & v19_lattices(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc14_lattices)).
% 10.97/3.93  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 10.97/3.93  tff(f_213, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (k2_lattice3(A) = k8_filter_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_lattice3)).
% 10.97/3.93  tff(f_120, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(k1_domain_1(u1_struct_0(A), u1_struct_0(A), B, C), k8_filter_1(A)) <=> r3_lattices(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_filter_1)).
% 10.97/3.93  tff(c_72, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 10.97/3.93  tff(c_86, plain, (r3_lattices('#skF_2', '#skF_3', '#skF_4') | r3_orders_2(k3_lattice3('#skF_2'), k4_lattice3('#skF_2', '#skF_3'), k4_lattice3('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 10.97/3.93  tff(c_91, plain, (r3_orders_2(k3_lattice3('#skF_2'), k4_lattice3('#skF_2', '#skF_3'), k4_lattice3('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_86])).
% 10.97/3.93  tff(c_80, plain, (~r3_orders_2(k3_lattice3('#skF_2'), k4_lattice3('#skF_2', '#skF_3'), k4_lattice3('#skF_2', '#skF_4')) | ~r3_lattices('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_231])).
% 10.97/3.93  tff(c_101, plain, (~r3_lattices('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_80])).
% 10.97/3.93  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 10.97/3.93  tff(c_76, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 10.97/3.93  tff(c_74, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 10.97/3.93  tff(c_46, plain, (![A_39]: (l1_orders_2(k3_lattice3(A_39)) | ~l3_lattices(A_39) | ~v10_lattices(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_175])).
% 10.97/3.93  tff(c_62, plain, (![A_42]: (v3_orders_2(k3_lattice3(A_42)) | ~l3_lattices(A_42) | ~v10_lattices(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_204])).
% 10.97/3.93  tff(c_143, plain, (![A_68, B_69]: (k4_lattice3(A_68, B_69)=B_69 | ~m1_subset_1(B_69, u1_struct_0(A_68)) | ~l3_lattices(A_68) | ~v10_lattices(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.97/3.93  tff(c_149, plain, (k4_lattice3('#skF_2', '#skF_3')='#skF_3' | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_143])).
% 10.97/3.93  tff(c_156, plain, (k4_lattice3('#skF_2', '#skF_3')='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_149])).
% 10.97/3.93  tff(c_157, plain, (k4_lattice3('#skF_2', '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_78, c_156])).
% 10.97/3.93  tff(c_199, plain, (![A_79, B_80]: (m1_subset_1(k4_lattice3(A_79, B_80), u1_struct_0(k3_lattice3(A_79))) | ~m1_subset_1(B_80, u1_struct_0(A_79)) | ~l3_lattices(A_79) | ~v10_lattices(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.97/3.93  tff(c_205, plain, (m1_subset_1('#skF_3', u1_struct_0(k3_lattice3('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_157, c_199])).
% 10.97/3.93  tff(c_211, plain, (m1_subset_1('#skF_3', u1_struct_0(k3_lattice3('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_205])).
% 10.97/3.93  tff(c_212, plain, (m1_subset_1('#skF_3', u1_struct_0(k3_lattice3('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_78, c_211])).
% 10.97/3.93  tff(c_70, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 10.97/3.93  tff(c_146, plain, (k4_lattice3('#skF_2', '#skF_4')='#skF_4' | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_143])).
% 10.97/3.93  tff(c_152, plain, (k4_lattice3('#skF_2', '#skF_4')='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_146])).
% 10.97/3.93  tff(c_153, plain, (k4_lattice3('#skF_2', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_78, c_152])).
% 10.97/3.93  tff(c_208, plain, (m1_subset_1('#skF_4', u1_struct_0(k3_lattice3('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_153, c_199])).
% 10.97/3.93  tff(c_214, plain, (m1_subset_1('#skF_4', u1_struct_0(k3_lattice3('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_208])).
% 10.97/3.93  tff(c_215, plain, (m1_subset_1('#skF_4', u1_struct_0(k3_lattice3('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_78, c_214])).
% 10.97/3.93  tff(c_158, plain, (r3_orders_2(k3_lattice3('#skF_2'), k4_lattice3('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_91])).
% 10.97/3.93  tff(c_167, plain, (r3_orders_2(k3_lattice3('#skF_2'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_158])).
% 10.97/3.93  tff(c_861, plain, (![A_179, B_180, C_181]: (r1_orders_2(A_179, B_180, C_181) | ~r3_orders_2(A_179, B_180, C_181) | ~m1_subset_1(C_181, u1_struct_0(A_179)) | ~m1_subset_1(B_180, u1_struct_0(A_179)) | ~l1_orders_2(A_179) | ~v3_orders_2(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.97/3.93  tff(c_863, plain, (r1_orders_2(k3_lattice3('#skF_2'), '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0(k3_lattice3('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k3_lattice3('#skF_2'))) | ~l1_orders_2(k3_lattice3('#skF_2')) | ~v3_orders_2(k3_lattice3('#skF_2')) | v2_struct_0(k3_lattice3('#skF_2'))), inference(resolution, [status(thm)], [c_167, c_861])).
% 10.97/3.93  tff(c_866, plain, (r1_orders_2(k3_lattice3('#skF_2'), '#skF_3', '#skF_4') | ~l1_orders_2(k3_lattice3('#skF_2')) | ~v3_orders_2(k3_lattice3('#skF_2')) | v2_struct_0(k3_lattice3('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_215, c_863])).
% 10.97/3.93  tff(c_867, plain, (~v3_orders_2(k3_lattice3('#skF_2'))), inference(splitLeft, [status(thm)], [c_866])).
% 10.97/3.93  tff(c_870, plain, (~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_867])).
% 10.97/3.93  tff(c_873, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_870])).
% 10.97/3.93  tff(c_875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_873])).
% 10.97/3.93  tff(c_876, plain, (~l1_orders_2(k3_lattice3('#skF_2')) | v2_struct_0(k3_lattice3('#skF_2')) | r1_orders_2(k3_lattice3('#skF_2'), '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_866])).
% 10.97/3.93  tff(c_878, plain, (~l1_orders_2(k3_lattice3('#skF_2'))), inference(splitLeft, [status(thm)], [c_876])).
% 10.97/3.93  tff(c_881, plain, (~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_878])).
% 10.97/3.93  tff(c_884, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_881])).
% 10.97/3.93  tff(c_886, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_884])).
% 10.97/3.93  tff(c_887, plain, (r1_orders_2(k3_lattice3('#skF_2'), '#skF_3', '#skF_4') | v2_struct_0(k3_lattice3('#skF_2'))), inference(splitRight, [status(thm)], [c_876])).
% 10.97/3.93  tff(c_913, plain, (v2_struct_0(k3_lattice3('#skF_2'))), inference(splitLeft, [status(thm)], [c_887])).
% 10.97/3.93  tff(c_66, plain, (![A_42]: (~v2_struct_0(k3_lattice3(A_42)) | ~l3_lattices(A_42) | ~v10_lattices(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_204])).
% 10.97/3.93  tff(c_916, plain, (~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_913, c_66])).
% 10.97/3.93  tff(c_919, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_916])).
% 10.97/3.93  tff(c_921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_919])).
% 10.97/3.93  tff(c_922, plain, (r1_orders_2(k3_lattice3('#skF_2'), '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_887])).
% 10.97/3.93  tff(c_64, plain, (![A_42]: (v1_orders_2(k3_lattice3(A_42)) | ~l3_lattices(A_42) | ~v10_lattices(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_204])).
% 10.97/3.93  tff(c_36, plain, (![A_38]: (m1_subset_1(k2_lattice3(A_38), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38), u1_struct_0(A_38)))) | ~l3_lattices(A_38) | ~v10_lattices(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_158])).
% 10.97/3.93  tff(c_4, plain, (![A_4]: (g1_orders_2(u1_struct_0(A_4), u1_orders_2(A_4))=A_4 | ~v1_orders_2(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.97/3.93  tff(c_32, plain, (![A_34]: (g1_orders_2(u1_struct_0(A_34), k2_lattice3(A_34))=k3_lattice3(A_34) | ~l3_lattices(A_34) | ~v10_lattices(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.97/3.93  tff(c_185, plain, (![C_74, A_75, D_76, B_77]: (C_74=A_75 | g1_orders_2(C_74, D_76)!=g1_orders_2(A_75, B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(k2_zfmisc_1(A_75, A_75))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.97/3.93  tff(c_1143, plain, (![A_209, C_210, D_211]: (u1_struct_0(A_209)=C_210 | k3_lattice3(A_209)!=g1_orders_2(C_210, D_211) | ~m1_subset_1(k2_lattice3(A_209), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_209), u1_struct_0(A_209)))) | ~l3_lattices(A_209) | ~v10_lattices(A_209) | v2_struct_0(A_209))), inference(superposition, [status(thm), theory('equality')], [c_32, c_185])).
% 10.97/3.93  tff(c_1159, plain, (![A_218, A_217]: (u1_struct_0(A_218)=u1_struct_0(A_217) | k3_lattice3(A_218)!=A_217 | ~m1_subset_1(k2_lattice3(A_218), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_218), u1_struct_0(A_218)))) | ~l3_lattices(A_218) | ~v10_lattices(A_218) | v2_struct_0(A_218) | ~v1_orders_2(A_217) | ~l1_orders_2(A_217))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1143])).
% 10.97/3.93  tff(c_1164, plain, (![A_220, A_219]: (u1_struct_0(A_220)=u1_struct_0(A_219) | k3_lattice3(A_219)!=A_220 | ~v1_orders_2(A_220) | ~l1_orders_2(A_220) | ~l3_lattices(A_219) | ~v10_lattices(A_219) | v2_struct_0(A_219))), inference(resolution, [status(thm)], [c_36, c_1159])).
% 10.97/3.93  tff(c_1168, plain, (![A_221, A_222]: (u1_struct_0(k3_lattice3(A_221))=u1_struct_0(A_222) | k3_lattice3(A_222)!=k3_lattice3(A_221) | ~l1_orders_2(k3_lattice3(A_221)) | ~l3_lattices(A_222) | ~v10_lattices(A_222) | v2_struct_0(A_222) | ~l3_lattices(A_221) | ~v10_lattices(A_221) | v2_struct_0(A_221))), inference(resolution, [status(thm)], [c_64, c_1164])).
% 10.97/3.93  tff(c_1177, plain, (![A_39, A_222]: (u1_struct_0(k3_lattice3(A_39))=u1_struct_0(A_222) | k3_lattice3(A_39)!=k3_lattice3(A_222) | ~l3_lattices(A_222) | ~v10_lattices(A_222) | v2_struct_0(A_222) | ~l3_lattices(A_39) | ~v10_lattices(A_39) | v2_struct_0(A_39))), inference(resolution, [status(thm)], [c_46, c_1168])).
% 10.97/3.93  tff(c_888, plain, (l1_orders_2(k3_lattice3('#skF_2'))), inference(splitRight, [status(thm)], [c_876])).
% 10.97/3.93  tff(c_1170, plain, (![A_222]: (u1_struct_0(k3_lattice3('#skF_2'))=u1_struct_0(A_222) | k3_lattice3(A_222)!=k3_lattice3('#skF_2') | ~l3_lattices(A_222) | ~v10_lattices(A_222) | v2_struct_0(A_222) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_888, c_1168])).
% 10.97/3.93  tff(c_1175, plain, (![A_222]: (u1_struct_0(k3_lattice3('#skF_2'))=u1_struct_0(A_222) | k3_lattice3(A_222)!=k3_lattice3('#skF_2') | ~l3_lattices(A_222) | ~v10_lattices(A_222) | v2_struct_0(A_222) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1170])).
% 10.97/3.93  tff(c_1178, plain, (![A_223]: (u1_struct_0(k3_lattice3('#skF_2'))=u1_struct_0(A_223) | k3_lattice3(A_223)!=k3_lattice3('#skF_2') | ~l3_lattices(A_223) | ~v10_lattices(A_223) | v2_struct_0(A_223))), inference(negUnitSimplification, [status(thm)], [c_78, c_1175])).
% 10.97/3.93  tff(c_1281, plain, (![A_223]: (g1_orders_2(u1_struct_0(A_223), u1_orders_2(k3_lattice3('#skF_2')))=k3_lattice3('#skF_2') | ~v1_orders_2(k3_lattice3('#skF_2')) | ~l1_orders_2(k3_lattice3('#skF_2')) | k3_lattice3(A_223)!=k3_lattice3('#skF_2') | ~l3_lattices(A_223) | ~v10_lattices(A_223) | v2_struct_0(A_223))), inference(superposition, [status(thm), theory('equality')], [c_1178, c_4])).
% 10.97/3.93  tff(c_1314, plain, (![A_223]: (g1_orders_2(u1_struct_0(A_223), u1_orders_2(k3_lattice3('#skF_2')))=k3_lattice3('#skF_2') | ~v1_orders_2(k3_lattice3('#skF_2')) | k3_lattice3(A_223)!=k3_lattice3('#skF_2') | ~l3_lattices(A_223) | ~v10_lattices(A_223) | v2_struct_0(A_223))), inference(demodulation, [status(thm), theory('equality')], [c_888, c_1281])).
% 10.97/3.93  tff(c_2140, plain, (~v1_orders_2(k3_lattice3('#skF_2'))), inference(splitLeft, [status(thm)], [c_1314])).
% 10.97/3.93  tff(c_2143, plain, (~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_2140])).
% 10.97/3.93  tff(c_2146, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_2143])).
% 10.97/3.93  tff(c_2148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_2146])).
% 10.97/3.93  tff(c_2150, plain, (v1_orders_2(k3_lattice3('#skF_2'))), inference(splitRight, [status(thm)], [c_1314])).
% 10.97/3.93  tff(c_172, plain, (![D_70, B_71, C_72, A_73]: (D_70=B_71 | g1_orders_2(C_72, D_70)!=g1_orders_2(A_73, B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(k2_zfmisc_1(A_73, A_73))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.97/3.93  tff(c_1148, plain, (![A_212, D_213, C_214]: (k2_lattice3(A_212)=D_213 | k3_lattice3(A_212)!=g1_orders_2(C_214, D_213) | ~m1_subset_1(k2_lattice3(A_212), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_212), u1_struct_0(A_212)))) | ~l3_lattices(A_212) | ~v10_lattices(A_212) | v2_struct_0(A_212))), inference(superposition, [status(thm), theory('equality')], [c_32, c_172])).
% 10.97/3.93  tff(c_1152, plain, (![A_4, A_212]: (u1_orders_2(A_4)=k2_lattice3(A_212) | k3_lattice3(A_212)!=A_4 | ~m1_subset_1(k2_lattice3(A_212), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_212), u1_struct_0(A_212)))) | ~l3_lattices(A_212) | ~v10_lattices(A_212) | v2_struct_0(A_212) | ~v1_orders_2(A_4) | ~l1_orders_2(A_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1148])).
% 10.97/3.93  tff(c_3835, plain, (![A_310]: (u1_orders_2(k3_lattice3(A_310))=k2_lattice3(A_310) | ~m1_subset_1(k2_lattice3(A_310), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_310), u1_struct_0(A_310)))) | ~l3_lattices(A_310) | ~v10_lattices(A_310) | v2_struct_0(A_310) | ~v1_orders_2(k3_lattice3(A_310)) | ~l1_orders_2(k3_lattice3(A_310)))), inference(reflexivity, [status(thm), theory('equality')], [c_1152])).
% 10.97/3.93  tff(c_3887, plain, (![A_311]: (u1_orders_2(k3_lattice3(A_311))=k2_lattice3(A_311) | ~v1_orders_2(k3_lattice3(A_311)) | ~l1_orders_2(k3_lattice3(A_311)) | ~l3_lattices(A_311) | ~v10_lattices(A_311) | v2_struct_0(A_311))), inference(resolution, [status(thm)], [c_36, c_3835])).
% 10.97/3.93  tff(c_3890, plain, (u1_orders_2(k3_lattice3('#skF_2'))=k2_lattice3('#skF_2') | ~l1_orders_2(k3_lattice3('#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2150, c_3887])).
% 10.97/3.93  tff(c_3896, plain, (u1_orders_2(k3_lattice3('#skF_2'))=k2_lattice3('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_888, c_3890])).
% 10.97/3.93  tff(c_3897, plain, (u1_orders_2(k3_lattice3('#skF_2'))=k2_lattice3('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_78, c_3896])).
% 10.97/3.93  tff(c_3921, plain, (g1_orders_2(u1_struct_0(k3_lattice3('#skF_2')), k2_lattice3('#skF_2'))=k3_lattice3('#skF_2') | ~v1_orders_2(k3_lattice3('#skF_2')) | ~l1_orders_2(k3_lattice3('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3897, c_4])).
% 10.97/3.93  tff(c_3932, plain, (g1_orders_2(u1_struct_0(k3_lattice3('#skF_2')), k2_lattice3('#skF_2'))=k3_lattice3('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_888, c_2150, c_3921])).
% 10.97/3.93  tff(c_4098, plain, (![A_222]: (g1_orders_2(u1_struct_0(A_222), k2_lattice3('#skF_2'))=k3_lattice3('#skF_2') | k3_lattice3(A_222)!=k3_lattice3('#skF_2') | ~l3_lattices(A_222) | ~v10_lattices(A_222) | v2_struct_0(A_222) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1177, c_3932])).
% 10.97/3.93  tff(c_4148, plain, (![A_222]: (g1_orders_2(u1_struct_0(A_222), k2_lattice3('#skF_2'))=k3_lattice3('#skF_2') | k3_lattice3(A_222)!=k3_lattice3('#skF_2') | ~l3_lattices(A_222) | ~v10_lattices(A_222) | v2_struct_0(A_222) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_4098])).
% 10.97/3.93  tff(c_4150, plain, (![A_314]: (g1_orders_2(u1_struct_0(A_314), k2_lattice3('#skF_2'))=k3_lattice3('#skF_2') | k3_lattice3(A_314)!=k3_lattice3('#skF_2') | ~l3_lattices(A_314) | ~v10_lattices(A_314) | v2_struct_0(A_314))), inference(negUnitSimplification, [status(thm)], [c_78, c_4148])).
% 10.97/3.93  tff(c_2186, plain, (![A_242]: (g1_orders_2(u1_struct_0(A_242), u1_orders_2(k3_lattice3('#skF_2')))=k3_lattice3('#skF_2') | k3_lattice3(A_242)!=k3_lattice3('#skF_2') | ~l3_lattices(A_242) | ~v10_lattices(A_242) | v2_struct_0(A_242))), inference(splitRight, [status(thm)], [c_1314])).
% 10.97/3.93  tff(c_10, plain, (![D_17, B_13, C_16, A_12]: (D_17=B_13 | g1_orders_2(C_16, D_17)!=g1_orders_2(A_12, B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(k2_zfmisc_1(A_12, A_12))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.97/3.93  tff(c_2215, plain, (![B_13, A_12, A_242]: (u1_orders_2(k3_lattice3('#skF_2'))=B_13 | g1_orders_2(A_12, B_13)!=k3_lattice3('#skF_2') | ~m1_subset_1(B_13, k1_zfmisc_1(k2_zfmisc_1(A_12, A_12))) | k3_lattice3(A_242)!=k3_lattice3('#skF_2') | ~l3_lattices(A_242) | ~v10_lattices(A_242) | v2_struct_0(A_242))), inference(superposition, [status(thm), theory('equality')], [c_2186, c_10])).
% 10.97/3.93  tff(c_2834, plain, (![A_276]: (k3_lattice3(A_276)!=k3_lattice3('#skF_2') | ~l3_lattices(A_276) | ~v10_lattices(A_276) | v2_struct_0(A_276))), inference(splitLeft, [status(thm)], [c_2215])).
% 10.97/3.93  tff(c_2843, plain, (~l3_lattices('#skF_2') | ~v10_lattices('#skF_2')), inference(resolution, [status(thm)], [c_2834, c_78])).
% 10.97/3.93  tff(c_2849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_2843])).
% 10.97/3.93  tff(c_2851, plain, (![B_277, A_278]: (u1_orders_2(k3_lattice3('#skF_2'))=B_277 | g1_orders_2(A_278, B_277)!=k3_lattice3('#skF_2') | ~m1_subset_1(B_277, k1_zfmisc_1(k2_zfmisc_1(A_278, A_278))))), inference(splitRight, [status(thm)], [c_2215])).
% 10.97/3.93  tff(c_2875, plain, (![A_282]: (u1_orders_2(k3_lattice3('#skF_2'))=k2_lattice3(A_282) | g1_orders_2(u1_struct_0(A_282), k2_lattice3(A_282))!=k3_lattice3('#skF_2') | ~l3_lattices(A_282) | ~v10_lattices(A_282) | v2_struct_0(A_282))), inference(resolution, [status(thm)], [c_36, c_2851])).
% 10.97/3.93  tff(c_2913, plain, (![A_283]: (u1_orders_2(k3_lattice3('#skF_2'))=k2_lattice3(A_283) | k3_lattice3(A_283)!=k3_lattice3('#skF_2') | ~l3_lattices(A_283) | ~v10_lattices(A_283) | v2_struct_0(A_283) | ~l3_lattices(A_283) | ~v10_lattices(A_283) | v2_struct_0(A_283))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2875])).
% 10.97/3.93  tff(c_2954, plain, (![A_283]: (g1_orders_2(u1_struct_0(k3_lattice3('#skF_2')), k2_lattice3(A_283))=k3_lattice3('#skF_2') | ~v1_orders_2(k3_lattice3('#skF_2')) | ~l1_orders_2(k3_lattice3('#skF_2')) | k3_lattice3(A_283)!=k3_lattice3('#skF_2') | ~l3_lattices(A_283) | ~v10_lattices(A_283) | v2_struct_0(A_283) | ~l3_lattices(A_283) | ~v10_lattices(A_283) | v2_struct_0(A_283))), inference(superposition, [status(thm), theory('equality')], [c_2913, c_4])).
% 10.97/3.93  tff(c_3087, plain, (![A_287]: (g1_orders_2(u1_struct_0(k3_lattice3('#skF_2')), k2_lattice3(A_287))=k3_lattice3('#skF_2') | k3_lattice3(A_287)!=k3_lattice3('#skF_2') | ~l3_lattices(A_287) | ~v10_lattices(A_287) | v2_struct_0(A_287))), inference(demodulation, [status(thm), theory('equality')], [c_888, c_2150, c_2954])).
% 10.97/3.93  tff(c_12, plain, (![C_16, A_12, D_17, B_13]: (C_16=A_12 | g1_orders_2(C_16, D_17)!=g1_orders_2(A_12, B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(k2_zfmisc_1(A_12, A_12))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.97/3.93  tff(c_3115, plain, (![A_12, B_13, A_287]: (u1_struct_0(k3_lattice3('#skF_2'))=A_12 | g1_orders_2(A_12, B_13)!=k3_lattice3('#skF_2') | ~m1_subset_1(B_13, k1_zfmisc_1(k2_zfmisc_1(A_12, A_12))) | k3_lattice3(A_287)!=k3_lattice3('#skF_2') | ~l3_lattices(A_287) | ~v10_lattices(A_287) | v2_struct_0(A_287))), inference(superposition, [status(thm), theory('equality')], [c_3087, c_12])).
% 10.97/3.93  tff(c_3664, plain, (![A_304]: (k3_lattice3(A_304)!=k3_lattice3('#skF_2') | ~l3_lattices(A_304) | ~v10_lattices(A_304) | v2_struct_0(A_304))), inference(splitLeft, [status(thm)], [c_3115])).
% 10.97/3.93  tff(c_3673, plain, (~l3_lattices('#skF_2') | ~v10_lattices('#skF_2')), inference(resolution, [status(thm)], [c_3664, c_78])).
% 10.97/3.93  tff(c_3679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_3673])).
% 10.97/3.93  tff(c_3681, plain, (![A_305, B_306]: (u1_struct_0(k3_lattice3('#skF_2'))=A_305 | g1_orders_2(A_305, B_306)!=k3_lattice3('#skF_2') | ~m1_subset_1(B_306, k1_zfmisc_1(k2_zfmisc_1(A_305, A_305))))), inference(splitRight, [status(thm)], [c_3115])).
% 10.97/3.93  tff(c_3685, plain, (![A_38]: (u1_struct_0(k3_lattice3('#skF_2'))=u1_struct_0(A_38) | g1_orders_2(u1_struct_0(A_38), k2_lattice3(A_38))!=k3_lattice3('#skF_2') | ~l3_lattices(A_38) | ~v10_lattices(A_38) | v2_struct_0(A_38))), inference(resolution, [status(thm)], [c_36, c_3681])).
% 10.97/3.93  tff(c_4172, plain, (u1_struct_0(k3_lattice3('#skF_2'))=u1_struct_0('#skF_2') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4150, c_3685])).
% 10.97/3.93  tff(c_4268, plain, (u1_struct_0(k3_lattice3('#skF_2'))=u1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_4172])).
% 10.97/3.93  tff(c_4269, plain, (u1_struct_0(k3_lattice3('#skF_2'))=u1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_78, c_4268])).
% 10.97/3.93  tff(c_8, plain, (![B_9, C_11, A_5]: (r2_hidden(k4_tarski(B_9, C_11), u1_orders_2(A_5)) | ~r1_orders_2(A_5, B_9, C_11) | ~m1_subset_1(C_11, u1_struct_0(A_5)) | ~m1_subset_1(B_9, u1_struct_0(A_5)) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.97/3.93  tff(c_3918, plain, (![B_9, C_11]: (r2_hidden(k4_tarski(B_9, C_11), k2_lattice3('#skF_2')) | ~r1_orders_2(k3_lattice3('#skF_2'), B_9, C_11) | ~m1_subset_1(C_11, u1_struct_0(k3_lattice3('#skF_2'))) | ~m1_subset_1(B_9, u1_struct_0(k3_lattice3('#skF_2'))) | ~l1_orders_2(k3_lattice3('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3897, c_8])).
% 10.97/3.93  tff(c_3930, plain, (![B_9, C_11]: (r2_hidden(k4_tarski(B_9, C_11), k2_lattice3('#skF_2')) | ~r1_orders_2(k3_lattice3('#skF_2'), B_9, C_11) | ~m1_subset_1(C_11, u1_struct_0(k3_lattice3('#skF_2'))) | ~m1_subset_1(B_9, u1_struct_0(k3_lattice3('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_888, c_3918])).
% 10.97/3.93  tff(c_6692, plain, (![B_369, C_370]: (r2_hidden(k4_tarski(B_369, C_370), k2_lattice3('#skF_2')) | ~r1_orders_2(k3_lattice3('#skF_2'), B_369, C_370) | ~m1_subset_1(C_370, u1_struct_0('#skF_2')) | ~m1_subset_1(B_369, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4269, c_4269, c_3930])).
% 10.97/3.93  tff(c_249, plain, (![A_88, B_89, C_90, D_91]: (k1_domain_1(A_88, B_89, C_90, D_91)=k4_tarski(C_90, D_91) | ~m1_subset_1(D_91, B_89) | ~m1_subset_1(C_90, A_88) | v1_xboole_0(B_89) | v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.97/3.93  tff(c_269, plain, (![A_88, C_90]: (k1_domain_1(A_88, u1_struct_0('#skF_2'), C_90, '#skF_4')=k4_tarski(C_90, '#skF_4') | ~m1_subset_1(C_90, A_88) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(A_88))), inference(resolution, [status(thm)], [c_70, c_249])).
% 10.97/3.93  tff(c_271, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_269])).
% 10.97/3.93  tff(c_128, plain, (![A_65]: (m1_subset_1('#skF_1'(A_65), k1_zfmisc_1(u1_struct_0(A_65))) | ~l3_lattices(A_65) | ~v10_lattices(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.97/3.93  tff(c_2, plain, (![B_3, A_1]: (v1_xboole_0(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.97/3.93  tff(c_132, plain, (![A_65]: (v1_xboole_0('#skF_1'(A_65)) | ~v1_xboole_0(u1_struct_0(A_65)) | ~l3_lattices(A_65) | ~v10_lattices(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_128, c_2])).
% 10.97/3.93  tff(c_274, plain, (v1_xboole_0('#skF_1'('#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_271, c_132])).
% 10.97/3.93  tff(c_277, plain, (v1_xboole_0('#skF_1'('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_274])).
% 10.97/3.93  tff(c_278, plain, (v1_xboole_0('#skF_1'('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_78, c_277])).
% 10.97/3.93  tff(c_24, plain, (![A_25]: (~v1_xboole_0('#skF_1'(A_25)) | ~l3_lattices(A_25) | ~v10_lattices(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.97/3.93  tff(c_281, plain, (~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_278, c_24])).
% 10.97/3.93  tff(c_284, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_281])).
% 10.97/3.93  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_284])).
% 10.97/3.93  tff(c_288, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_269])).
% 10.97/3.93  tff(c_112, plain, (![A_63]: (k8_filter_1(A_63)=k2_lattice3(A_63) | ~l3_lattices(A_63) | ~v10_lattices(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_213])).
% 10.97/3.93  tff(c_118, plain, (k8_filter_1('#skF_2')=k2_lattice3('#skF_2') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2')), inference(resolution, [status(thm)], [c_112, c_78])).
% 10.97/3.93  tff(c_122, plain, (k8_filter_1('#skF_2')=k2_lattice3('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_118])).
% 10.97/3.93  tff(c_287, plain, (![A_88, C_90]: (k1_domain_1(A_88, u1_struct_0('#skF_2'), C_90, '#skF_4')=k4_tarski(C_90, '#skF_4') | ~m1_subset_1(C_90, A_88) | v1_xboole_0(A_88))), inference(splitRight, [status(thm)], [c_269])).
% 10.97/3.93  tff(c_939, plain, (![A_188, B_189, C_190]: (r3_lattices(A_188, B_189, C_190) | ~r2_hidden(k1_domain_1(u1_struct_0(A_188), u1_struct_0(A_188), B_189, C_190), k8_filter_1(A_188)) | ~m1_subset_1(C_190, u1_struct_0(A_188)) | ~m1_subset_1(B_189, u1_struct_0(A_188)) | ~l3_lattices(A_188) | ~v10_lattices(A_188) | v2_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.97/3.93  tff(c_955, plain, (![C_90]: (r3_lattices('#skF_2', C_90, '#skF_4') | ~r2_hidden(k4_tarski(C_90, '#skF_4'), k8_filter_1('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1(C_90, u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_90, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_287, c_939])).
% 10.97/3.93  tff(c_969, plain, (![C_90]: (r3_lattices('#skF_2', C_90, '#skF_4') | ~r2_hidden(k4_tarski(C_90, '#skF_4'), k2_lattice3('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_90, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_122, c_955])).
% 10.97/3.93  tff(c_970, plain, (![C_90]: (r3_lattices('#skF_2', C_90, '#skF_4') | ~r2_hidden(k4_tarski(C_90, '#skF_4'), k2_lattice3('#skF_2')) | ~m1_subset_1(C_90, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_288, c_78, c_969])).
% 10.97/3.93  tff(c_6703, plain, (![B_369]: (r3_lattices('#skF_2', B_369, '#skF_4') | ~r1_orders_2(k3_lattice3('#skF_2'), B_369, '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1(B_369, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_6692, c_970])).
% 10.97/3.93  tff(c_6743, plain, (![B_374]: (r3_lattices('#skF_2', B_374, '#skF_4') | ~r1_orders_2(k3_lattice3('#skF_2'), B_374, '#skF_4') | ~m1_subset_1(B_374, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_6703])).
% 10.97/3.93  tff(c_6749, plain, (r3_lattices('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_922, c_6743])).
% 10.97/3.93  tff(c_6753, plain, (r3_lattices('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6749])).
% 10.97/3.93  tff(c_6755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_6753])).
% 10.97/3.93  tff(c_6756, plain, (r3_lattices('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_86])).
% 10.97/3.93  tff(c_6883, plain, (![A_404, B_405, C_406, D_407]: (k1_domain_1(A_404, B_405, C_406, D_407)=k4_tarski(C_406, D_407) | ~m1_subset_1(D_407, B_405) | ~m1_subset_1(C_406, A_404) | v1_xboole_0(B_405) | v1_xboole_0(A_404))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.97/3.93  tff(c_6897, plain, (![A_404, C_406]: (k1_domain_1(A_404, u1_struct_0('#skF_2'), C_406, '#skF_4')=k4_tarski(C_406, '#skF_4') | ~m1_subset_1(C_406, A_404) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(A_404))), inference(resolution, [status(thm)], [c_70, c_6883])).
% 10.97/3.93  tff(c_6914, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_6897])).
% 10.97/3.93  tff(c_6794, plain, (![A_387]: (m1_subset_1('#skF_1'(A_387), k1_zfmisc_1(u1_struct_0(A_387))) | ~l3_lattices(A_387) | ~v10_lattices(A_387) | v2_struct_0(A_387))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.97/3.93  tff(c_6798, plain, (![A_387]: (v1_xboole_0('#skF_1'(A_387)) | ~v1_xboole_0(u1_struct_0(A_387)) | ~l3_lattices(A_387) | ~v10_lattices(A_387) | v2_struct_0(A_387))), inference(resolution, [status(thm)], [c_6794, c_2])).
% 10.97/3.93  tff(c_6917, plain, (v1_xboole_0('#skF_1'('#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_6914, c_6798])).
% 10.97/3.93  tff(c_6920, plain, (v1_xboole_0('#skF_1'('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_6917])).
% 10.97/3.93  tff(c_6921, plain, (v1_xboole_0('#skF_1'('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_78, c_6920])).
% 10.97/3.93  tff(c_6924, plain, (~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_6921, c_24])).
% 10.97/3.93  tff(c_6927, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_6924])).
% 10.97/3.93  tff(c_6929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_6927])).
% 10.97/3.93  tff(c_6931, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_6897])).
% 10.97/3.93  tff(c_6778, plain, (![A_385]: (k8_filter_1(A_385)=k2_lattice3(A_385) | ~l3_lattices(A_385) | ~v10_lattices(A_385) | v2_struct_0(A_385))), inference(cnfTransformation, [status(thm)], [f_213])).
% 10.97/3.93  tff(c_6784, plain, (k8_filter_1('#skF_2')=k2_lattice3('#skF_2') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2')), inference(resolution, [status(thm)], [c_6778, c_78])).
% 10.97/3.93  tff(c_6788, plain, (k8_filter_1('#skF_2')=k2_lattice3('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_6784])).
% 10.97/3.93  tff(c_6930, plain, (![A_404, C_406]: (k1_domain_1(A_404, u1_struct_0('#skF_2'), C_406, '#skF_4')=k4_tarski(C_406, '#skF_4') | ~m1_subset_1(C_406, A_404) | v1_xboole_0(A_404))), inference(splitRight, [status(thm)], [c_6897])).
% 10.97/3.93  tff(c_7771, plain, (![A_540, B_541, C_542]: (r2_hidden(k1_domain_1(u1_struct_0(A_540), u1_struct_0(A_540), B_541, C_542), k8_filter_1(A_540)) | ~r3_lattices(A_540, B_541, C_542) | ~m1_subset_1(C_542, u1_struct_0(A_540)) | ~m1_subset_1(B_541, u1_struct_0(A_540)) | ~l3_lattices(A_540) | ~v10_lattices(A_540) | v2_struct_0(A_540))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.97/3.93  tff(c_7790, plain, (![C_406]: (r2_hidden(k4_tarski(C_406, '#skF_4'), k8_filter_1('#skF_2')) | ~r3_lattices('#skF_2', C_406, '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1(C_406, u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_406, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_6930, c_7771])).
% 10.97/3.93  tff(c_7805, plain, (![C_406]: (r2_hidden(k4_tarski(C_406, '#skF_4'), k2_lattice3('#skF_2')) | ~r3_lattices('#skF_2', C_406, '#skF_4') | v2_struct_0('#skF_2') | ~m1_subset_1(C_406, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_6788, c_7790])).
% 10.97/3.93  tff(c_7806, plain, (![C_406]: (r2_hidden(k4_tarski(C_406, '#skF_4'), k2_lattice3('#skF_2')) | ~r3_lattices('#skF_2', C_406, '#skF_4') | ~m1_subset_1(C_406, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_6931, c_78, c_7805])).
% 10.97/3.93  tff(c_6835, plain, (![A_398, B_399]: (k4_lattice3(A_398, B_399)=B_399 | ~m1_subset_1(B_399, u1_struct_0(A_398)) | ~l3_lattices(A_398) | ~v10_lattices(A_398) | v2_struct_0(A_398))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.97/3.93  tff(c_6841, plain, (k4_lattice3('#skF_2', '#skF_3')='#skF_3' | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_6835])).
% 10.97/3.93  tff(c_6848, plain, (k4_lattice3('#skF_2', '#skF_3')='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_6841])).
% 10.97/3.93  tff(c_6849, plain, (k4_lattice3('#skF_2', '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_78, c_6848])).
% 10.97/3.93  tff(c_6866, plain, (![A_402, B_403]: (m1_subset_1(k4_lattice3(A_402, B_403), u1_struct_0(k3_lattice3(A_402))) | ~m1_subset_1(B_403, u1_struct_0(A_402)) | ~l3_lattices(A_402) | ~v10_lattices(A_402) | v2_struct_0(A_402))), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.97/3.93  tff(c_6872, plain, (m1_subset_1('#skF_3', u1_struct_0(k3_lattice3('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6849, c_6866])).
% 10.97/3.93  tff(c_6878, plain, (m1_subset_1('#skF_3', u1_struct_0(k3_lattice3('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_6872])).
% 10.97/3.93  tff(c_6879, plain, (m1_subset_1('#skF_3', u1_struct_0(k3_lattice3('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_78, c_6878])).
% 10.97/3.93  tff(c_7607, plain, (![A_511, B_512, C_513]: (r3_orders_2(A_511, B_512, C_513) | ~r1_orders_2(A_511, B_512, C_513) | ~m1_subset_1(C_513, u1_struct_0(A_511)) | ~m1_subset_1(B_512, u1_struct_0(A_511)) | ~l1_orders_2(A_511) | ~v3_orders_2(A_511) | v2_struct_0(A_511))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.97/3.93  tff(c_7619, plain, (![B_512]: (r3_orders_2(k3_lattice3('#skF_2'), B_512, '#skF_3') | ~r1_orders_2(k3_lattice3('#skF_2'), B_512, '#skF_3') | ~m1_subset_1(B_512, u1_struct_0(k3_lattice3('#skF_2'))) | ~l1_orders_2(k3_lattice3('#skF_2')) | ~v3_orders_2(k3_lattice3('#skF_2')) | v2_struct_0(k3_lattice3('#skF_2')))), inference(resolution, [status(thm)], [c_6879, c_7607])).
% 10.97/3.93  tff(c_7664, plain, (~v3_orders_2(k3_lattice3('#skF_2'))), inference(splitLeft, [status(thm)], [c_7619])).
% 10.97/3.93  tff(c_7667, plain, (~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_7664])).
% 10.97/3.93  tff(c_7670, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_7667])).
% 10.97/3.93  tff(c_7672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_7670])).
% 10.97/3.93  tff(c_7673, plain, (![B_512]: (~l1_orders_2(k3_lattice3('#skF_2')) | v2_struct_0(k3_lattice3('#skF_2')) | r3_orders_2(k3_lattice3('#skF_2'), B_512, '#skF_3') | ~r1_orders_2(k3_lattice3('#skF_2'), B_512, '#skF_3') | ~m1_subset_1(B_512, u1_struct_0(k3_lattice3('#skF_2'))))), inference(splitRight, [status(thm)], [c_7619])).
% 10.97/3.93  tff(c_7675, plain, (~l1_orders_2(k3_lattice3('#skF_2'))), inference(splitLeft, [status(thm)], [c_7673])).
% 10.97/3.93  tff(c_7678, plain, (~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_7675])).
% 10.97/3.93  tff(c_7681, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_7678])).
% 10.97/3.93  tff(c_7683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_7681])).
% 10.97/3.93  tff(c_7685, plain, (l1_orders_2(k3_lattice3('#skF_2'))), inference(splitRight, [status(thm)], [c_7673])).
% 10.97/3.93  tff(c_6813, plain, (![C_390, A_391, D_392, B_393]: (C_390=A_391 | g1_orders_2(C_390, D_392)!=g1_orders_2(A_391, B_393) | ~m1_subset_1(B_393, k1_zfmisc_1(k2_zfmisc_1(A_391, A_391))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.97/3.93  tff(c_7872, plain, (![A_550, C_551, D_552]: (u1_struct_0(A_550)=C_551 | k3_lattice3(A_550)!=g1_orders_2(C_551, D_552) | ~m1_subset_1(k2_lattice3(A_550), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_550), u1_struct_0(A_550)))) | ~l3_lattices(A_550) | ~v10_lattices(A_550) | v2_struct_0(A_550))), inference(superposition, [status(thm), theory('equality')], [c_32, c_6813])).
% 10.97/3.93  tff(c_7940, plain, (![A_565, A_564]: (u1_struct_0(A_565)=u1_struct_0(A_564) | k3_lattice3(A_564)!=A_565 | ~m1_subset_1(k2_lattice3(A_564), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_564), u1_struct_0(A_564)))) | ~l3_lattices(A_564) | ~v10_lattices(A_564) | v2_struct_0(A_564) | ~v1_orders_2(A_565) | ~l1_orders_2(A_565))), inference(superposition, [status(thm), theory('equality')], [c_4, c_7872])).
% 10.97/3.93  tff(c_7975, plain, (![A_569, A_568]: (u1_struct_0(A_569)=u1_struct_0(A_568) | k3_lattice3(A_569)!=A_568 | ~v1_orders_2(A_568) | ~l1_orders_2(A_568) | ~l3_lattices(A_569) | ~v10_lattices(A_569) | v2_struct_0(A_569))), inference(resolution, [status(thm)], [c_36, c_7940])).
% 10.97/3.93  tff(c_7979, plain, (![A_570, A_571]: (u1_struct_0(k3_lattice3(A_570))=u1_struct_0(A_571) | k3_lattice3(A_571)!=k3_lattice3(A_570) | ~l1_orders_2(k3_lattice3(A_570)) | ~l3_lattices(A_571) | ~v10_lattices(A_571) | v2_struct_0(A_571) | ~l3_lattices(A_570) | ~v10_lattices(A_570) | v2_struct_0(A_570))), inference(resolution, [status(thm)], [c_64, c_7975])).
% 10.97/3.93  tff(c_7988, plain, (![A_39, A_571]: (u1_struct_0(k3_lattice3(A_39))=u1_struct_0(A_571) | k3_lattice3(A_571)!=k3_lattice3(A_39) | ~l3_lattices(A_571) | ~v10_lattices(A_571) | v2_struct_0(A_571) | ~l3_lattices(A_39) | ~v10_lattices(A_39) | v2_struct_0(A_39))), inference(resolution, [status(thm)], [c_46, c_7979])).
% 10.97/3.93  tff(c_7981, plain, (![A_571]: (u1_struct_0(k3_lattice3('#skF_2'))=u1_struct_0(A_571) | k3_lattice3(A_571)!=k3_lattice3('#skF_2') | ~l3_lattices(A_571) | ~v10_lattices(A_571) | v2_struct_0(A_571) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_7685, c_7979])).
% 10.97/3.93  tff(c_7986, plain, (![A_571]: (u1_struct_0(k3_lattice3('#skF_2'))=u1_struct_0(A_571) | k3_lattice3(A_571)!=k3_lattice3('#skF_2') | ~l3_lattices(A_571) | ~v10_lattices(A_571) | v2_struct_0(A_571) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_7981])).
% 10.97/3.93  tff(c_7989, plain, (![A_572]: (u1_struct_0(k3_lattice3('#skF_2'))=u1_struct_0(A_572) | k3_lattice3(A_572)!=k3_lattice3('#skF_2') | ~l3_lattices(A_572) | ~v10_lattices(A_572) | v2_struct_0(A_572))), inference(negUnitSimplification, [status(thm)], [c_78, c_7986])).
% 10.97/3.93  tff(c_8098, plain, (![A_572]: (g1_orders_2(u1_struct_0(A_572), u1_orders_2(k3_lattice3('#skF_2')))=k3_lattice3('#skF_2') | ~v1_orders_2(k3_lattice3('#skF_2')) | ~l1_orders_2(k3_lattice3('#skF_2')) | k3_lattice3(A_572)!=k3_lattice3('#skF_2') | ~l3_lattices(A_572) | ~v10_lattices(A_572) | v2_struct_0(A_572))), inference(superposition, [status(thm), theory('equality')], [c_7989, c_4])).
% 10.97/3.93  tff(c_8132, plain, (![A_572]: (g1_orders_2(u1_struct_0(A_572), u1_orders_2(k3_lattice3('#skF_2')))=k3_lattice3('#skF_2') | ~v1_orders_2(k3_lattice3('#skF_2')) | k3_lattice3(A_572)!=k3_lattice3('#skF_2') | ~l3_lattices(A_572) | ~v10_lattices(A_572) | v2_struct_0(A_572))), inference(demodulation, [status(thm), theory('equality')], [c_7685, c_8098])).
% 10.97/3.93  tff(c_8987, plain, (~v1_orders_2(k3_lattice3('#skF_2'))), inference(splitLeft, [status(thm)], [c_8132])).
% 10.97/3.93  tff(c_8990, plain, (~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_8987])).
% 10.97/3.93  tff(c_8993, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_8990])).
% 10.97/3.93  tff(c_8995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_8993])).
% 10.97/3.93  tff(c_8997, plain, (v1_orders_2(k3_lattice3('#skF_2'))), inference(splitRight, [status(thm)], [c_8132])).
% 10.97/3.93  tff(c_9054, plain, (![A_593]: (g1_orders_2(u1_struct_0(A_593), u1_orders_2(k3_lattice3('#skF_2')))=k3_lattice3('#skF_2') | k3_lattice3(A_593)!=k3_lattice3('#skF_2') | ~l3_lattices(A_593) | ~v10_lattices(A_593) | v2_struct_0(A_593))), inference(splitRight, [status(thm)], [c_8132])).
% 10.97/3.93  tff(c_9079, plain, (![B_13, A_12, A_593]: (u1_orders_2(k3_lattice3('#skF_2'))=B_13 | g1_orders_2(A_12, B_13)!=k3_lattice3('#skF_2') | ~m1_subset_1(B_13, k1_zfmisc_1(k2_zfmisc_1(A_12, A_12))) | k3_lattice3(A_593)!=k3_lattice3('#skF_2') | ~l3_lattices(A_593) | ~v10_lattices(A_593) | v2_struct_0(A_593))), inference(superposition, [status(thm), theory('equality')], [c_9054, c_10])).
% 10.97/3.93  tff(c_9620, plain, (![A_623]: (k3_lattice3(A_623)!=k3_lattice3('#skF_2') | ~l3_lattices(A_623) | ~v10_lattices(A_623) | v2_struct_0(A_623))), inference(splitLeft, [status(thm)], [c_9079])).
% 10.97/3.93  tff(c_9629, plain, (~l3_lattices('#skF_2') | ~v10_lattices('#skF_2')), inference(resolution, [status(thm)], [c_9620, c_78])).
% 10.97/3.93  tff(c_9635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_9629])).
% 10.97/3.93  tff(c_9637, plain, (![B_624, A_625]: (u1_orders_2(k3_lattice3('#skF_2'))=B_624 | g1_orders_2(A_625, B_624)!=k3_lattice3('#skF_2') | ~m1_subset_1(B_624, k1_zfmisc_1(k2_zfmisc_1(A_625, A_625))))), inference(splitRight, [status(thm)], [c_9079])).
% 10.97/3.93  tff(c_9642, plain, (![A_626]: (u1_orders_2(k3_lattice3('#skF_2'))=k2_lattice3(A_626) | g1_orders_2(u1_struct_0(A_626), k2_lattice3(A_626))!=k3_lattice3('#skF_2') | ~l3_lattices(A_626) | ~v10_lattices(A_626) | v2_struct_0(A_626))), inference(resolution, [status(thm)], [c_36, c_9637])).
% 10.97/3.93  tff(c_9680, plain, (![A_627]: (u1_orders_2(k3_lattice3('#skF_2'))=k2_lattice3(A_627) | k3_lattice3(A_627)!=k3_lattice3('#skF_2') | ~l3_lattices(A_627) | ~v10_lattices(A_627) | v2_struct_0(A_627) | ~l3_lattices(A_627) | ~v10_lattices(A_627) | v2_struct_0(A_627))), inference(superposition, [status(thm), theory('equality')], [c_32, c_9642])).
% 10.97/3.93  tff(c_9721, plain, (![A_627]: (g1_orders_2(u1_struct_0(k3_lattice3('#skF_2')), k2_lattice3(A_627))=k3_lattice3('#skF_2') | ~v1_orders_2(k3_lattice3('#skF_2')) | ~l1_orders_2(k3_lattice3('#skF_2')) | k3_lattice3(A_627)!=k3_lattice3('#skF_2') | ~l3_lattices(A_627) | ~v10_lattices(A_627) | v2_struct_0(A_627) | ~l3_lattices(A_627) | ~v10_lattices(A_627) | v2_struct_0(A_627))), inference(superposition, [status(thm), theory('equality')], [c_9680, c_4])).
% 10.97/3.93  tff(c_9854, plain, (![A_631]: (g1_orders_2(u1_struct_0(k3_lattice3('#skF_2')), k2_lattice3(A_631))=k3_lattice3('#skF_2') | k3_lattice3(A_631)!=k3_lattice3('#skF_2') | ~l3_lattices(A_631) | ~v10_lattices(A_631) | v2_struct_0(A_631))), inference(demodulation, [status(thm), theory('equality')], [c_7685, c_8997, c_9721])).
% 10.97/3.93  tff(c_9913, plain, (![A_571, A_631]: (g1_orders_2(u1_struct_0(A_571), k2_lattice3(A_631))=k3_lattice3('#skF_2') | k3_lattice3(A_631)!=k3_lattice3('#skF_2') | ~l3_lattices(A_631) | ~v10_lattices(A_631) | v2_struct_0(A_631) | k3_lattice3(A_571)!=k3_lattice3('#skF_2') | ~l3_lattices(A_571) | ~v10_lattices(A_571) | v2_struct_0(A_571) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7988, c_9854])).
% 10.97/3.93  tff(c_9928, plain, (![A_571, A_631]: (g1_orders_2(u1_struct_0(A_571), k2_lattice3(A_631))=k3_lattice3('#skF_2') | k3_lattice3(A_631)!=k3_lattice3('#skF_2') | ~l3_lattices(A_631) | ~v10_lattices(A_631) | v2_struct_0(A_631) | k3_lattice3(A_571)!=k3_lattice3('#skF_2') | ~l3_lattices(A_571) | ~v10_lattices(A_571) | v2_struct_0(A_571) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_9913])).
% 10.97/3.93  tff(c_9929, plain, (![A_571, A_631]: (g1_orders_2(u1_struct_0(A_571), k2_lattice3(A_631))=k3_lattice3('#skF_2') | k3_lattice3(A_631)!=k3_lattice3('#skF_2') | ~l3_lattices(A_631) | ~v10_lattices(A_631) | v2_struct_0(A_631) | k3_lattice3(A_571)!=k3_lattice3('#skF_2') | ~l3_lattices(A_571) | ~v10_lattices(A_571) | v2_struct_0(A_571))), inference(negUnitSimplification, [status(thm)], [c_78, c_9928])).
% 10.97/3.93  tff(c_10777, plain, (![A_656, A_657]: (g1_orders_2(u1_struct_0(A_656), k2_lattice3(A_657))=k3_lattice3('#skF_2') | k3_lattice3(A_657)!=k3_lattice3('#skF_2') | ~l3_lattices(A_657) | ~v10_lattices(A_657) | v2_struct_0(A_657) | k3_lattice3(A_656)!=k3_lattice3('#skF_2') | ~l3_lattices(A_656) | ~v10_lattices(A_656) | v2_struct_0(A_656))), inference(negUnitSimplification, [status(thm)], [c_78, c_9928])).
% 10.97/3.93  tff(c_6819, plain, (![A_4, A_391, B_393]: (u1_struct_0(A_4)=A_391 | g1_orders_2(A_391, B_393)!=A_4 | ~m1_subset_1(B_393, k1_zfmisc_1(k2_zfmisc_1(A_391, A_391))) | ~v1_orders_2(A_4) | ~l1_orders_2(A_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_6813])).
% 10.97/3.93  tff(c_7592, plain, (![A_507, B_508]: (u1_struct_0(g1_orders_2(A_507, B_508))=A_507 | ~m1_subset_1(B_508, k1_zfmisc_1(k2_zfmisc_1(A_507, A_507))) | ~v1_orders_2(g1_orders_2(A_507, B_508)) | ~l1_orders_2(g1_orders_2(A_507, B_508)))), inference(reflexivity, [status(thm), theory('equality')], [c_6819])).
% 10.97/3.93  tff(c_7596, plain, (![A_38]: (u1_struct_0(g1_orders_2(u1_struct_0(A_38), k2_lattice3(A_38)))=u1_struct_0(A_38) | ~v1_orders_2(g1_orders_2(u1_struct_0(A_38), k2_lattice3(A_38))) | ~l1_orders_2(g1_orders_2(u1_struct_0(A_38), k2_lattice3(A_38))) | ~l3_lattices(A_38) | ~v10_lattices(A_38) | v2_struct_0(A_38))), inference(resolution, [status(thm)], [c_36, c_7592])).
% 10.97/3.93  tff(c_10784, plain, (![A_657]: (u1_struct_0(g1_orders_2(u1_struct_0(A_657), k2_lattice3(A_657)))=u1_struct_0(A_657) | ~v1_orders_2(k3_lattice3('#skF_2')) | ~l1_orders_2(g1_orders_2(u1_struct_0(A_657), k2_lattice3(A_657))) | ~l3_lattices(A_657) | ~v10_lattices(A_657) | v2_struct_0(A_657) | k3_lattice3(A_657)!=k3_lattice3('#skF_2') | ~l3_lattices(A_657) | ~v10_lattices(A_657) | v2_struct_0(A_657) | k3_lattice3(A_657)!=k3_lattice3('#skF_2') | ~l3_lattices(A_657) | ~v10_lattices(A_657) | v2_struct_0(A_657))), inference(superposition, [status(thm), theory('equality')], [c_10777, c_7596])).
% 10.97/3.93  tff(c_10909, plain, (![A_658]: (u1_struct_0(g1_orders_2(u1_struct_0(A_658), k2_lattice3(A_658)))=u1_struct_0(A_658) | ~l1_orders_2(g1_orders_2(u1_struct_0(A_658), k2_lattice3(A_658))) | k3_lattice3(A_658)!=k3_lattice3('#skF_2') | ~l3_lattices(A_658) | ~v10_lattices(A_658) | v2_struct_0(A_658))), inference(demodulation, [status(thm), theory('equality')], [c_8997, c_10784])).
% 10.97/3.93  tff(c_10913, plain, (![A_631]: (u1_struct_0(g1_orders_2(u1_struct_0(A_631), k2_lattice3(A_631)))=u1_struct_0(A_631) | ~l1_orders_2(k3_lattice3('#skF_2')) | k3_lattice3(A_631)!=k3_lattice3('#skF_2') | ~l3_lattices(A_631) | ~v10_lattices(A_631) | v2_struct_0(A_631) | k3_lattice3(A_631)!=k3_lattice3('#skF_2') | ~l3_lattices(A_631) | ~v10_lattices(A_631) | v2_struct_0(A_631) | k3_lattice3(A_631)!=k3_lattice3('#skF_2') | ~l3_lattices(A_631) | ~v10_lattices(A_631) | v2_struct_0(A_631))), inference(superposition, [status(thm), theory('equality')], [c_9929, c_10909])).
% 10.97/3.93  tff(c_10963, plain, (![A_659]: (u1_struct_0(g1_orders_2(u1_struct_0(A_659), k2_lattice3(A_659)))=u1_struct_0(A_659) | k3_lattice3(A_659)!=k3_lattice3('#skF_2') | ~l3_lattices(A_659) | ~v10_lattices(A_659) | v2_struct_0(A_659))), inference(demodulation, [status(thm), theory('equality')], [c_7685, c_10913])).
% 10.97/3.93  tff(c_11165, plain, (![A_660]: (u1_struct_0(k3_lattice3(A_660))=u1_struct_0(A_660) | k3_lattice3(A_660)!=k3_lattice3('#skF_2') | ~l3_lattices(A_660) | ~v10_lattices(A_660) | v2_struct_0(A_660) | ~l3_lattices(A_660) | ~v10_lattices(A_660) | v2_struct_0(A_660))), inference(superposition, [status(thm), theory('equality')], [c_32, c_10963])).
% 10.97/3.93  tff(c_8071, plain, (![A_572]: (g1_orders_2(u1_struct_0(k3_lattice3('#skF_2')), k2_lattice3(A_572))=k3_lattice3(A_572) | ~l3_lattices(A_572) | ~v10_lattices(A_572) | v2_struct_0(A_572) | k3_lattice3(A_572)!=k3_lattice3('#skF_2') | ~l3_lattices(A_572) | ~v10_lattices(A_572) | v2_struct_0(A_572))), inference(superposition, [status(thm), theory('equality')], [c_7989, c_32])).
% 10.97/3.93  tff(c_11210, plain, (![A_572]: (g1_orders_2(u1_struct_0('#skF_2'), k2_lattice3(A_572))=k3_lattice3(A_572) | k3_lattice3(A_572)!=k3_lattice3('#skF_2') | ~l3_lattices(A_572) | ~v10_lattices(A_572) | v2_struct_0(A_572) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_11165, c_8071])).
% 10.97/3.93  tff(c_11370, plain, (![A_572]: (g1_orders_2(u1_struct_0('#skF_2'), k2_lattice3(A_572))=k3_lattice3(A_572) | k3_lattice3(A_572)!=k3_lattice3('#skF_2') | ~l3_lattices(A_572) | ~v10_lattices(A_572) | v2_struct_0(A_572) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_11210])).
% 10.97/3.93  tff(c_11467, plain, (![A_667]: (g1_orders_2(u1_struct_0('#skF_2'), k2_lattice3(A_667))=k3_lattice3(A_667) | k3_lattice3(A_667)!=k3_lattice3('#skF_2') | ~l3_lattices(A_667) | ~v10_lattices(A_667) | v2_struct_0(A_667))), inference(negUnitSimplification, [status(thm)], [c_78, c_11370])).
% 10.97/3.93  tff(c_10957, plain, (![A_631]: (u1_struct_0(g1_orders_2(u1_struct_0(A_631), k2_lattice3(A_631)))=u1_struct_0(A_631) | k3_lattice3(A_631)!=k3_lattice3('#skF_2') | ~l3_lattices(A_631) | ~v10_lattices(A_631) | v2_struct_0(A_631))), inference(demodulation, [status(thm), theory('equality')], [c_7685, c_10913])).
% 10.97/3.93  tff(c_11474, plain, (u1_struct_0(k3_lattice3('#skF_2'))=u1_struct_0('#skF_2') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11467, c_10957])).
% 10.97/3.93  tff(c_11572, plain, (u1_struct_0(k3_lattice3('#skF_2'))=u1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_11474])).
% 10.97/3.93  tff(c_11573, plain, (u1_struct_0(k3_lattice3('#skF_2'))=u1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_78, c_11572])).
% 10.97/3.93  tff(c_9641, plain, (![A_38]: (u1_orders_2(k3_lattice3('#skF_2'))=k2_lattice3(A_38) | g1_orders_2(u1_struct_0(A_38), k2_lattice3(A_38))!=k3_lattice3('#skF_2') | ~l3_lattices(A_38) | ~v10_lattices(A_38) | v2_struct_0(A_38))), inference(resolution, [status(thm)], [c_36, c_9637])).
% 10.97/3.93  tff(c_11514, plain, (u1_orders_2(k3_lattice3('#skF_2'))=k2_lattice3('#skF_2') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11467, c_9641])).
% 10.97/3.93  tff(c_11597, plain, (u1_orders_2(k3_lattice3('#skF_2'))=k2_lattice3('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_11514])).
% 10.97/3.93  tff(c_11598, plain, (u1_orders_2(k3_lattice3('#skF_2'))=k2_lattice3('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_78, c_11597])).
% 10.97/3.93  tff(c_6, plain, (![A_5, B_9, C_11]: (r1_orders_2(A_5, B_9, C_11) | ~r2_hidden(k4_tarski(B_9, C_11), u1_orders_2(A_5)) | ~m1_subset_1(C_11, u1_struct_0(A_5)) | ~m1_subset_1(B_9, u1_struct_0(A_5)) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.97/3.93  tff(c_11886, plain, (![B_9, C_11]: (r1_orders_2(k3_lattice3('#skF_2'), B_9, C_11) | ~r2_hidden(k4_tarski(B_9, C_11), k2_lattice3('#skF_2')) | ~m1_subset_1(C_11, u1_struct_0(k3_lattice3('#skF_2'))) | ~m1_subset_1(B_9, u1_struct_0(k3_lattice3('#skF_2'))) | ~l1_orders_2(k3_lattice3('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_11598, c_6])).
% 10.97/3.93  tff(c_13416, plain, (![B_698, C_699]: (r1_orders_2(k3_lattice3('#skF_2'), B_698, C_699) | ~r2_hidden(k4_tarski(B_698, C_699), k2_lattice3('#skF_2')) | ~m1_subset_1(C_699, u1_struct_0('#skF_2')) | ~m1_subset_1(B_698, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_7685, c_11573, c_11573, c_11886])).
% 10.97/3.93  tff(c_13421, plain, (![C_406]: (r1_orders_2(k3_lattice3('#skF_2'), C_406, '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~r3_lattices('#skF_2', C_406, '#skF_4') | ~m1_subset_1(C_406, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_7806, c_13416])).
% 10.97/3.93  tff(c_13456, plain, (![C_703]: (r1_orders_2(k3_lattice3('#skF_2'), C_703, '#skF_4') | ~r3_lattices('#skF_2', C_703, '#skF_4') | ~m1_subset_1(C_703, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_13421])).
% 10.97/3.93  tff(c_6838, plain, (k4_lattice3('#skF_2', '#skF_4')='#skF_4' | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_6835])).
% 10.97/3.93  tff(c_6844, plain, (k4_lattice3('#skF_2', '#skF_4')='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_6838])).
% 10.97/3.93  tff(c_6845, plain, (k4_lattice3('#skF_2', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_78, c_6844])).
% 10.97/3.93  tff(c_6760, plain, (~r3_orders_2(k3_lattice3('#skF_2'), k4_lattice3('#skF_2', '#skF_3'), k4_lattice3('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6756, c_80])).
% 10.97/3.93  tff(c_6850, plain, (~r3_orders_2(k3_lattice3('#skF_2'), k4_lattice3('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6845, c_6760])).
% 10.97/3.93  tff(c_6859, plain, (~r3_orders_2(k3_lattice3('#skF_2'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6849, c_6850])).
% 10.97/3.93  tff(c_7684, plain, (![B_512]: (v2_struct_0(k3_lattice3('#skF_2')) | r3_orders_2(k3_lattice3('#skF_2'), B_512, '#skF_3') | ~r1_orders_2(k3_lattice3('#skF_2'), B_512, '#skF_3') | ~m1_subset_1(B_512, u1_struct_0(k3_lattice3('#skF_2'))))), inference(splitRight, [status(thm)], [c_7673])).
% 10.97/3.93  tff(c_7723, plain, (v2_struct_0(k3_lattice3('#skF_2'))), inference(splitLeft, [status(thm)], [c_7684])).
% 10.97/3.93  tff(c_7741, plain, (~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_7723, c_66])).
% 10.97/3.93  tff(c_7744, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_7741])).
% 10.97/3.93  tff(c_7746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_7744])).
% 10.97/3.93  tff(c_7748, plain, (~v2_struct_0(k3_lattice3('#skF_2'))), inference(splitRight, [status(thm)], [c_7684])).
% 10.97/3.93  tff(c_7674, plain, (v3_orders_2(k3_lattice3('#skF_2'))), inference(splitRight, [status(thm)], [c_7619])).
% 10.97/3.93  tff(c_6875, plain, (m1_subset_1('#skF_4', u1_struct_0(k3_lattice3('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6845, c_6866])).
% 10.97/3.93  tff(c_6881, plain, (m1_subset_1('#skF_4', u1_struct_0(k3_lattice3('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_6875])).
% 10.97/3.93  tff(c_6882, plain, (m1_subset_1('#skF_4', u1_struct_0(k3_lattice3('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_78, c_6881])).
% 10.97/3.93  tff(c_7618, plain, (![B_512]: (r3_orders_2(k3_lattice3('#skF_2'), B_512, '#skF_4') | ~r1_orders_2(k3_lattice3('#skF_2'), B_512, '#skF_4') | ~m1_subset_1(B_512, u1_struct_0(k3_lattice3('#skF_2'))) | ~l1_orders_2(k3_lattice3('#skF_2')) | ~v3_orders_2(k3_lattice3('#skF_2')) | v2_struct_0(k3_lattice3('#skF_2')))), inference(resolution, [status(thm)], [c_6882, c_7607])).
% 10.97/3.93  tff(c_7878, plain, (![B_512]: (r3_orders_2(k3_lattice3('#skF_2'), B_512, '#skF_4') | ~r1_orders_2(k3_lattice3('#skF_2'), B_512, '#skF_4') | ~m1_subset_1(B_512, u1_struct_0(k3_lattice3('#skF_2'))) | v2_struct_0(k3_lattice3('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_7674, c_7685, c_7618])).
% 10.97/3.93  tff(c_7880, plain, (![B_553]: (r3_orders_2(k3_lattice3('#skF_2'), B_553, '#skF_4') | ~r1_orders_2(k3_lattice3('#skF_2'), B_553, '#skF_4') | ~m1_subset_1(B_553, u1_struct_0(k3_lattice3('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_7748, c_7878])).
% 10.97/3.93  tff(c_7886, plain, (r3_orders_2(k3_lattice3('#skF_2'), '#skF_3', '#skF_4') | ~r1_orders_2(k3_lattice3('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_6879, c_7880])).
% 10.97/3.93  tff(c_7894, plain, (~r1_orders_2(k3_lattice3('#skF_2'), '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_6859, c_7886])).
% 10.97/3.93  tff(c_13462, plain, (~r3_lattices('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_13456, c_7894])).
% 10.97/3.93  tff(c_13469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_6756, c_13462])).
% 10.97/3.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.97/3.93  
% 10.97/3.93  Inference rules
% 10.97/3.93  ----------------------
% 10.97/3.93  #Ref     : 27
% 10.97/3.93  #Sup     : 3247
% 10.97/3.93  #Fact    : 14
% 10.97/3.93  #Define  : 0
% 10.97/3.93  #Split   : 53
% 10.97/3.93  #Chain   : 0
% 10.97/3.93  #Close   : 0
% 10.97/3.93  
% 10.97/3.93  Ordering : KBO
% 10.97/3.93  
% 10.97/3.93  Simplification rules
% 10.97/3.93  ----------------------
% 10.97/3.93  #Subsume      : 1262
% 10.97/3.93  #Demod        : 1774
% 10.97/3.93  #Tautology    : 507
% 10.97/3.93  #SimpNegUnit  : 841
% 10.97/3.93  #BackRed      : 57
% 10.97/3.93  
% 10.97/3.93  #Partial instantiations: 0
% 10.97/3.93  #Strategies tried      : 1
% 10.97/3.93  
% 10.97/3.93  Timing (in seconds)
% 10.97/3.93  ----------------------
% 10.97/3.93  Preprocessing        : 0.37
% 10.97/3.93  Parsing              : 0.19
% 10.97/3.93  CNF conversion       : 0.03
% 10.97/3.93  Main loop            : 2.74
% 10.97/3.93  Inferencing          : 0.80
% 10.97/3.93  Reduction            : 0.75
% 10.97/3.93  Demodulation         : 0.50
% 10.97/3.93  BG Simplification    : 0.10
% 10.97/3.93  Subsumption          : 0.94
% 10.97/3.93  Abstraction          : 0.15
% 10.97/3.93  MUC search           : 0.00
% 10.97/3.93  Cooper               : 0.00
% 10.97/3.93  Total                : 3.21
% 10.97/3.93  Index Insertion      : 0.00
% 10.97/3.93  Index Deletion       : 0.00
% 10.97/3.93  Index Matching       : 0.00
% 10.97/3.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
