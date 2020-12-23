%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:12 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 111 expanded)
%              Number of leaves         :   37 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  162 ( 425 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                   => r2_funct_2(u1_struct_0(C),u1_struct_0(B),D,k3_tmap_1(A,B,C,C,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_117,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_34,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_212,plain,(
    ! [A_110,B_111,D_112] :
      ( r2_funct_2(A_110,B_111,D_112,D_112)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_2(D_112,A_110,B_111)
      | ~ v1_funct_1(D_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_214,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_212])).

tff(c_223,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_214])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_64,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(A_72,B_73)
      | ~ m1_subset_1(A_72,k1_zfmisc_1(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_53,c_64])).

tff(c_246,plain,(
    ! [B_120,C_121,A_122] :
      ( m1_pre_topc(B_120,C_121)
      | ~ r1_tarski(u1_struct_0(B_120),u1_struct_0(C_121))
      | ~ m1_pre_topc(C_121,A_122)
      | ~ m1_pre_topc(B_120,A_122)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_251,plain,(
    ! [B_123,A_124] :
      ( m1_pre_topc(B_123,B_123)
      | ~ m1_pre_topc(B_123,A_124)
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124) ) ),
    inference(resolution,[status(thm)],[c_68,c_246])).

tff(c_253,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_251])).

tff(c_256,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_253])).

tff(c_79,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_79])).

tff(c_108,plain,(
    ! [C_87,A_88,B_89] :
      ( v4_relat_1(C_87,A_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_120,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_108])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( k7_relat_1(B_6,A_5) = B_6
      | ~ v4_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_125,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_10])).

tff(c_128,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_125])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_189,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k2_partfun1(A_105,B_106,C_107,D_108) = k7_relat_1(C_107,D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ v1_funct_1(C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_191,plain,(
    ! [D_108] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_108) = k7_relat_1('#skF_4',D_108)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_189])).

tff(c_200,plain,(
    ! [D_108] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_108) = k7_relat_1('#skF_4',D_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_191])).

tff(c_283,plain,(
    ! [B_140,D_138,A_137,E_136,C_139] :
      ( k3_tmap_1(A_137,B_140,C_139,D_138,E_136) = k2_partfun1(u1_struct_0(C_139),u1_struct_0(B_140),E_136,u1_struct_0(D_138))
      | ~ m1_pre_topc(D_138,C_139)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_139),u1_struct_0(B_140))))
      | ~ v1_funct_2(E_136,u1_struct_0(C_139),u1_struct_0(B_140))
      | ~ v1_funct_1(E_136)
      | ~ m1_pre_topc(D_138,A_137)
      | ~ m1_pre_topc(C_139,A_137)
      | ~ l1_pre_topc(B_140)
      | ~ v2_pre_topc(B_140)
      | v2_struct_0(B_140)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_285,plain,(
    ! [A_137,D_138] :
      ( k3_tmap_1(A_137,'#skF_2','#skF_3',D_138,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_138))
      | ~ m1_pre_topc(D_138,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_138,A_137)
      | ~ m1_pre_topc('#skF_3',A_137)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_32,c_283])).

tff(c_294,plain,(
    ! [D_138,A_137] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_138)) = k3_tmap_1(A_137,'#skF_2','#skF_3',D_138,'#skF_4')
      | ~ m1_pre_topc(D_138,'#skF_3')
      | ~ m1_pre_topc(D_138,A_137)
      | ~ m1_pre_topc('#skF_3',A_137)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_34,c_200,c_285])).

tff(c_305,plain,(
    ! [D_143,A_144] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_143)) = k3_tmap_1(A_144,'#skF_2','#skF_3',D_143,'#skF_4')
      | ~ m1_pre_topc(D_143,'#skF_3')
      | ~ m1_pre_topc(D_143,A_144)
      | ~ m1_pre_topc('#skF_3',A_144)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_294])).

tff(c_309,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_305])).

tff(c_316,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_38,c_256,c_128,c_309])).

tff(c_317,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_316])).

tff(c_30,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_318,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_30])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_318])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.69  
% 3.00/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.70  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.00/1.70  
% 3.00/1.70  %Foreground sorts:
% 3.00/1.70  
% 3.00/1.70  
% 3.00/1.70  %Background operators:
% 3.00/1.70  
% 3.00/1.70  
% 3.00/1.70  %Foreground operators:
% 3.00/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.00/1.70  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.00/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.00/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.70  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.00/1.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.00/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.00/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.00/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.00/1.70  tff('#skF_1', type, '#skF_1': $i).
% 3.00/1.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.00/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.00/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.00/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.00/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.70  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.00/1.70  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.00/1.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.00/1.70  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.00/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.00/1.70  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.00/1.70  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.00/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.70  
% 3.00/1.71  tff(f_148, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 3.00/1.71  tff(f_71, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.00/1.71  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.00/1.71  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.00/1.71  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.00/1.71  tff(f_117, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.00/1.71  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.00/1.71  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.00/1.71  tff(f_39, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.00/1.71  tff(f_55, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.00/1.71  tff(f_103, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.00/1.71  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.00/1.71  tff(c_34, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.00/1.71  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.00/1.71  tff(c_212, plain, (![A_110, B_111, D_112]: (r2_funct_2(A_110, B_111, D_112, D_112) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_2(D_112, A_110, B_111) | ~v1_funct_1(D_112))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.00/1.71  tff(c_214, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_212])).
% 3.00/1.71  tff(c_223, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_214])).
% 3.00/1.71  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.00/1.71  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.00/1.71  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.00/1.71  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.00/1.71  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.00/1.71  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.00/1.71  tff(c_53, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.00/1.71  tff(c_64, plain, (![A_72, B_73]: (r1_tarski(A_72, B_73) | ~m1_subset_1(A_72, k1_zfmisc_1(B_73)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.00/1.71  tff(c_68, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_53, c_64])).
% 3.00/1.71  tff(c_246, plain, (![B_120, C_121, A_122]: (m1_pre_topc(B_120, C_121) | ~r1_tarski(u1_struct_0(B_120), u1_struct_0(C_121)) | ~m1_pre_topc(C_121, A_122) | ~m1_pre_topc(B_120, A_122) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.00/1.71  tff(c_251, plain, (![B_123, A_124]: (m1_pre_topc(B_123, B_123) | ~m1_pre_topc(B_123, A_124) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124))), inference(resolution, [status(thm)], [c_68, c_246])).
% 3.00/1.71  tff(c_253, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_251])).
% 3.00/1.71  tff(c_256, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_253])).
% 3.00/1.71  tff(c_79, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.00/1.71  tff(c_91, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_79])).
% 3.00/1.71  tff(c_108, plain, (![C_87, A_88, B_89]: (v4_relat_1(C_87, A_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.00/1.71  tff(c_120, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_108])).
% 3.00/1.71  tff(c_10, plain, (![B_6, A_5]: (k7_relat_1(B_6, A_5)=B_6 | ~v4_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.00/1.71  tff(c_125, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_10])).
% 3.00/1.71  tff(c_128, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_125])).
% 3.00/1.71  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.00/1.71  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.00/1.71  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.00/1.71  tff(c_189, plain, (![A_105, B_106, C_107, D_108]: (k2_partfun1(A_105, B_106, C_107, D_108)=k7_relat_1(C_107, D_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~v1_funct_1(C_107))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.00/1.71  tff(c_191, plain, (![D_108]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_108)=k7_relat_1('#skF_4', D_108) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_189])).
% 3.00/1.71  tff(c_200, plain, (![D_108]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_108)=k7_relat_1('#skF_4', D_108))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_191])).
% 3.00/1.71  tff(c_283, plain, (![B_140, D_138, A_137, E_136, C_139]: (k3_tmap_1(A_137, B_140, C_139, D_138, E_136)=k2_partfun1(u1_struct_0(C_139), u1_struct_0(B_140), E_136, u1_struct_0(D_138)) | ~m1_pre_topc(D_138, C_139) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_139), u1_struct_0(B_140)))) | ~v1_funct_2(E_136, u1_struct_0(C_139), u1_struct_0(B_140)) | ~v1_funct_1(E_136) | ~m1_pre_topc(D_138, A_137) | ~m1_pre_topc(C_139, A_137) | ~l1_pre_topc(B_140) | ~v2_pre_topc(B_140) | v2_struct_0(B_140) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.00/1.71  tff(c_285, plain, (![A_137, D_138]: (k3_tmap_1(A_137, '#skF_2', '#skF_3', D_138, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_138)) | ~m1_pre_topc(D_138, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_138, A_137) | ~m1_pre_topc('#skF_3', A_137) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(resolution, [status(thm)], [c_32, c_283])).
% 3.00/1.71  tff(c_294, plain, (![D_138, A_137]: (k7_relat_1('#skF_4', u1_struct_0(D_138))=k3_tmap_1(A_137, '#skF_2', '#skF_3', D_138, '#skF_4') | ~m1_pre_topc(D_138, '#skF_3') | ~m1_pre_topc(D_138, A_137) | ~m1_pre_topc('#skF_3', A_137) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_34, c_200, c_285])).
% 3.00/1.71  tff(c_305, plain, (![D_143, A_144]: (k7_relat_1('#skF_4', u1_struct_0(D_143))=k3_tmap_1(A_144, '#skF_2', '#skF_3', D_143, '#skF_4') | ~m1_pre_topc(D_143, '#skF_3') | ~m1_pre_topc(D_143, A_144) | ~m1_pre_topc('#skF_3', A_144) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(negUnitSimplification, [status(thm)], [c_46, c_294])).
% 3.00/1.71  tff(c_309, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_305])).
% 3.00/1.71  tff(c_316, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_38, c_256, c_128, c_309])).
% 3.00/1.71  tff(c_317, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_316])).
% 3.00/1.71  tff(c_30, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.00/1.71  tff(c_318, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_317, c_30])).
% 3.00/1.71  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_318])).
% 3.00/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.71  
% 3.00/1.71  Inference rules
% 3.00/1.71  ----------------------
% 3.00/1.71  #Ref     : 0
% 3.00/1.71  #Sup     : 51
% 3.00/1.71  #Fact    : 0
% 3.00/1.71  #Define  : 0
% 3.00/1.71  #Split   : 1
% 3.00/1.71  #Chain   : 0
% 3.00/1.71  #Close   : 0
% 3.00/1.71  
% 3.00/1.71  Ordering : KBO
% 3.00/1.71  
% 3.00/1.71  Simplification rules
% 3.00/1.71  ----------------------
% 3.00/1.71  #Subsume      : 3
% 3.00/1.71  #Demod        : 40
% 3.00/1.71  #Tautology    : 21
% 3.00/1.71  #SimpNegUnit  : 3
% 3.00/1.71  #BackRed      : 1
% 3.00/1.71  
% 3.00/1.71  #Partial instantiations: 0
% 3.00/1.71  #Strategies tried      : 1
% 3.00/1.71  
% 3.00/1.71  Timing (in seconds)
% 3.00/1.71  ----------------------
% 3.00/1.72  Preprocessing        : 0.56
% 3.00/1.72  Parsing              : 0.29
% 3.00/1.72  CNF conversion       : 0.05
% 3.00/1.72  Main loop            : 0.33
% 3.00/1.72  Inferencing          : 0.12
% 3.00/1.72  Reduction            : 0.11
% 3.00/1.72  Demodulation         : 0.08
% 3.00/1.72  BG Simplification    : 0.03
% 3.00/1.72  Subsumption          : 0.06
% 3.00/1.72  Abstraction          : 0.02
% 3.00/1.72  MUC search           : 0.00
% 3.00/1.72  Cooper               : 0.00
% 3.00/1.72  Total                : 0.94
% 3.00/1.72  Index Insertion      : 0.00
% 3.00/1.72  Index Deletion       : 0.00
% 3.00/1.72  Index Matching       : 0.00
% 3.00/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
