%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:53 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 162 expanded)
%              Number of leaves         :   35 (  80 expanded)
%              Depth                    :   24
%              Number of atoms          :  371 ( 830 expanded)
%              Number of equality atoms :   33 ( 121 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_184,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_orders_1(C,k1_orders_1(u1_struct_0(A)))
               => ! [D] :
                    ( m2_orders_2(D,A,C)
                   => ( B = k1_funct_1(C,u1_struct_0(A))
                     => k3_orders_2(A,D,B) = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_orders_2)).

tff(f_74,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_130,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_159,axiom,(
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
                  ( m1_orders_1(D,k1_orders_1(u1_struct_0(A)))
                 => ! [E] :
                      ( m2_orders_2(E,A,D)
                     => ( ( r2_hidden(B,E)
                          & C = k1_funct_1(D,u1_struct_0(A)) )
                       => r3_orders_2(A,C,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_orders_2)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r1_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_orders_2)).

tff(c_26,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_30,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_42,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_40,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_38,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_36,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_32,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_89,plain,(
    ! [C_96,A_97,B_98] :
      ( m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m2_orders_2(C_96,A_97,B_98)
      | ~ m1_orders_1(B_98,k1_orders_1(u1_struct_0(A_97)))
      | ~ l1_orders_2(A_97)
      | ~ v5_orders_2(A_97)
      | ~ v4_orders_2(A_97)
      | ~ v3_orders_2(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_91,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_89])).

tff(c_94,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_32,c_91])).

tff(c_95,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_94])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] :
      ( m1_subset_1(k3_orders_2(A_4,B_5,C_6),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(C_6,u1_struct_0(A_4))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_orders_2(A_4)
      | ~ v5_orders_2(A_4)
      | ~ v4_orders_2(A_4)
      | ~ v3_orders_2(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    k1_funct_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [B_105,D_106,A_107,C_108] :
      ( r2_hidden(B_105,D_106)
      | ~ r2_hidden(B_105,k3_orders_2(A_107,D_106,C_108))
      | ~ m1_subset_1(D_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_subset_1(C_108,u1_struct_0(A_107))
      | ~ m1_subset_1(B_105,u1_struct_0(A_107))
      | ~ l1_orders_2(A_107)
      | ~ v5_orders_2(A_107)
      | ~ v4_orders_2(A_107)
      | ~ v3_orders_2(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_188,plain,(
    ! [A_139,A_140,D_141,C_142] :
      ( r2_hidden('#skF_1'(A_139,k3_orders_2(A_140,D_141,C_142)),D_141)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ m1_subset_1(C_142,u1_struct_0(A_140))
      | ~ m1_subset_1('#skF_1'(A_139,k3_orders_2(A_140,D_141,C_142)),u1_struct_0(A_140))
      | ~ l1_orders_2(A_140)
      | ~ v5_orders_2(A_140)
      | ~ v4_orders_2(A_140)
      | ~ v3_orders_2(A_140)
      | v2_struct_0(A_140)
      | k3_orders_2(A_140,D_141,C_142) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_140,D_141,C_142),k1_zfmisc_1(A_139)) ) ),
    inference(resolution,[status(thm)],[c_2,c_101])).

tff(c_200,plain,(
    ! [A_145,D_146,C_147] :
      ( r2_hidden('#skF_1'(u1_struct_0(A_145),k3_orders_2(A_145,D_146,C_147)),D_146)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ m1_subset_1(C_147,u1_struct_0(A_145))
      | ~ l1_orders_2(A_145)
      | ~ v5_orders_2(A_145)
      | ~ v4_orders_2(A_145)
      | ~ v3_orders_2(A_145)
      | v2_struct_0(A_145)
      | k3_orders_2(A_145,D_146,C_147) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_145,D_146,C_147),k1_zfmisc_1(u1_struct_0(A_145))) ) ),
    inference(resolution,[status(thm)],[c_4,c_188])).

tff(c_24,plain,(
    ! [A_36,D_64,B_52,E_66] :
      ( r3_orders_2(A_36,k1_funct_1(D_64,u1_struct_0(A_36)),B_52)
      | ~ r2_hidden(B_52,E_66)
      | ~ m2_orders_2(E_66,A_36,D_64)
      | ~ m1_orders_1(D_64,k1_orders_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(k1_funct_1(D_64,u1_struct_0(A_36)),u1_struct_0(A_36))
      | ~ m1_subset_1(B_52,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36)
      | ~ v5_orders_2(A_36)
      | ~ v4_orders_2(A_36)
      | ~ v3_orders_2(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_291,plain,(
    ! [A_190,D_193,A_192,D_194,C_191] :
      ( r3_orders_2(A_190,k1_funct_1(D_193,u1_struct_0(A_190)),'#skF_1'(u1_struct_0(A_192),k3_orders_2(A_192,D_194,C_191)))
      | ~ m2_orders_2(D_194,A_190,D_193)
      | ~ m1_orders_1(D_193,k1_orders_1(u1_struct_0(A_190)))
      | ~ m1_subset_1(k1_funct_1(D_193,u1_struct_0(A_190)),u1_struct_0(A_190))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_192),k3_orders_2(A_192,D_194,C_191)),u1_struct_0(A_190))
      | ~ l1_orders_2(A_190)
      | ~ v5_orders_2(A_190)
      | ~ v4_orders_2(A_190)
      | ~ v3_orders_2(A_190)
      | v2_struct_0(A_190)
      | ~ m1_subset_1(D_194,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ m1_subset_1(C_191,u1_struct_0(A_192))
      | ~ l1_orders_2(A_192)
      | ~ v5_orders_2(A_192)
      | ~ v4_orders_2(A_192)
      | ~ v3_orders_2(A_192)
      | v2_struct_0(A_192)
      | k3_orders_2(A_192,D_194,C_191) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_192,D_194,C_191),k1_zfmisc_1(u1_struct_0(A_192))) ) ),
    inference(resolution,[status(thm)],[c_200,c_24])).

tff(c_296,plain,(
    ! [A_192,D_194,C_191] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0(A_192),k3_orders_2(A_192,D_194,C_191)))
      | ~ m2_orders_2(D_194,'#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_192),k3_orders_2(A_192,D_194,C_191)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(D_194,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ m1_subset_1(C_191,u1_struct_0(A_192))
      | ~ l1_orders_2(A_192)
      | ~ v5_orders_2(A_192)
      | ~ v4_orders_2(A_192)
      | ~ v3_orders_2(A_192)
      | v2_struct_0(A_192)
      | k3_orders_2(A_192,D_194,C_191) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_192,D_194,C_191),k1_zfmisc_1(u1_struct_0(A_192))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_291])).

tff(c_299,plain,(
    ! [A_192,D_194,C_191] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0(A_192),k3_orders_2(A_192,D_194,C_191)))
      | ~ m2_orders_2(D_194,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_192),k3_orders_2(A_192,D_194,C_191)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(D_194,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ m1_subset_1(C_191,u1_struct_0(A_192))
      | ~ l1_orders_2(A_192)
      | ~ v5_orders_2(A_192)
      | ~ v4_orders_2(A_192)
      | ~ v3_orders_2(A_192)
      | v2_struct_0(A_192)
      | k3_orders_2(A_192,D_194,C_191) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_192,D_194,C_191),k1_zfmisc_1(u1_struct_0(A_192))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_28,c_32,c_296])).

tff(c_306,plain,(
    ! [A_200,D_201,C_202] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0(A_200),k3_orders_2(A_200,D_201,C_202)))
      | ~ m2_orders_2(D_201,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_200),k3_orders_2(A_200,D_201,C_202)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_201,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ m1_subset_1(C_202,u1_struct_0(A_200))
      | ~ l1_orders_2(A_200)
      | ~ v5_orders_2(A_200)
      | ~ v4_orders_2(A_200)
      | ~ v3_orders_2(A_200)
      | v2_struct_0(A_200)
      | k3_orders_2(A_200,D_201,C_202) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_200,D_201,C_202),k1_zfmisc_1(u1_struct_0(A_200))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_299])).

tff(c_310,plain,(
    ! [D_201,C_202] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_201,C_202)))
      | ~ m2_orders_2(D_201,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_201,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_202,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_201,C_202) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_201,C_202),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_306])).

tff(c_313,plain,(
    ! [D_201,C_202] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_201,C_202)))
      | ~ m2_orders_2(D_201,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_201,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_202,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_201,C_202) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_201,C_202),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_310])).

tff(c_315,plain,(
    ! [D_203,C_204] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_203,C_204)))
      | ~ m2_orders_2(D_203,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_203,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_204,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_203,C_204) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_203,C_204),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_313])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_orders_2(A_11,B_12,C_13)
      | ~ r3_orders_2(A_11,B_12,C_13)
      | ~ m1_subset_1(C_13,u1_struct_0(A_11))
      | ~ m1_subset_1(B_12,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11)
      | ~ v3_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_317,plain,(
    ! [D_203,C_204] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_203,C_204)))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_203,C_204)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(D_203,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_203,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_204,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_203,C_204) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_203,C_204),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_315,c_14])).

tff(c_320,plain,(
    ! [D_203,C_204] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_203,C_204)))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_203,C_204)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(D_203,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_203,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_204,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_203,C_204) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_203,C_204),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_34,c_317])).

tff(c_322,plain,(
    ! [D_205,C_206] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_205,C_206)))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_205,C_206)),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(D_205,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_205,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_206,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_205,C_206) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_205,C_206),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_320])).

tff(c_327,plain,(
    ! [D_207,C_208] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_207,C_208)))
      | ~ m2_orders_2(D_207,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_207,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_208,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_207,C_208) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_207,C_208),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_322])).

tff(c_106,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( r2_orders_2(A_109,B_110,C_111)
      | ~ r2_hidden(B_110,k3_orders_2(A_109,D_112,C_111))
      | ~ m1_subset_1(D_112,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_subset_1(C_111,u1_struct_0(A_109))
      | ~ m1_subset_1(B_110,u1_struct_0(A_109))
      | ~ l1_orders_2(A_109)
      | ~ v5_orders_2(A_109)
      | ~ v4_orders_2(A_109)
      | ~ v3_orders_2(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_226,plain,(
    ! [A_158,A_159,D_160,C_161] :
      ( r2_orders_2(A_158,'#skF_1'(A_159,k3_orders_2(A_158,D_160,C_161)),C_161)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ m1_subset_1(C_161,u1_struct_0(A_158))
      | ~ m1_subset_1('#skF_1'(A_159,k3_orders_2(A_158,D_160,C_161)),u1_struct_0(A_158))
      | ~ l1_orders_2(A_158)
      | ~ v5_orders_2(A_158)
      | ~ v4_orders_2(A_158)
      | ~ v3_orders_2(A_158)
      | v2_struct_0(A_158)
      | k3_orders_2(A_158,D_160,C_161) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_158,D_160,C_161),k1_zfmisc_1(A_159)) ) ),
    inference(resolution,[status(thm)],[c_2,c_106])).

tff(c_231,plain,(
    ! [A_162,D_163,C_164] :
      ( r2_orders_2(A_162,'#skF_1'(u1_struct_0(A_162),k3_orders_2(A_162,D_163,C_164)),C_164)
      | ~ m1_subset_1(D_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ m1_subset_1(C_164,u1_struct_0(A_162))
      | ~ l1_orders_2(A_162)
      | ~ v5_orders_2(A_162)
      | ~ v4_orders_2(A_162)
      | ~ v3_orders_2(A_162)
      | v2_struct_0(A_162)
      | k3_orders_2(A_162,D_163,C_164) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_162,D_163,C_164),k1_zfmisc_1(u1_struct_0(A_162))) ) ),
    inference(resolution,[status(thm)],[c_4,c_226])).

tff(c_16,plain,(
    ! [A_14,C_20,B_18] :
      ( ~ r2_orders_2(A_14,C_20,B_18)
      | ~ r1_orders_2(A_14,B_18,C_20)
      | ~ m1_subset_1(C_20,u1_struct_0(A_14))
      | ~ m1_subset_1(B_18,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v5_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_234,plain,(
    ! [A_162,C_164,D_163] :
      ( ~ r1_orders_2(A_162,C_164,'#skF_1'(u1_struct_0(A_162),k3_orders_2(A_162,D_163,C_164)))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_162),k3_orders_2(A_162,D_163,C_164)),u1_struct_0(A_162))
      | ~ m1_subset_1(D_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ m1_subset_1(C_164,u1_struct_0(A_162))
      | ~ l1_orders_2(A_162)
      | ~ v5_orders_2(A_162)
      | ~ v4_orders_2(A_162)
      | ~ v3_orders_2(A_162)
      | v2_struct_0(A_162)
      | k3_orders_2(A_162,D_163,C_164) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_162,D_163,C_164),k1_zfmisc_1(u1_struct_0(A_162))) ) ),
    inference(resolution,[status(thm)],[c_231,c_16])).

tff(c_330,plain,(
    ! [D_207] :
      ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_207,'#skF_3')),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(D_207,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_207,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_207,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_207,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_327,c_234])).

tff(c_333,plain,(
    ! [D_207] :
      ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_207,'#skF_3')),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(D_207,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_207,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',D_207,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_207,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42,c_40,c_38,c_36,c_330])).

tff(c_335,plain,(
    ! [D_209] :
      ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_209,'#skF_3')),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(D_209,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_209,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',D_209,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_209,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_333])).

tff(c_340,plain,(
    ! [D_210] :
      ( ~ m2_orders_2(D_210,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_210,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',D_210,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_210,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_335])).

tff(c_344,plain,(
    ! [B_5] :
      ( ~ m2_orders_2(B_5,'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_5,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_340])).

tff(c_347,plain,(
    ! [B_5] :
      ( ~ m2_orders_2(B_5,'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_5,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_344])).

tff(c_349,plain,(
    ! [B_211] :
      ( ~ m2_orders_2(B_211,'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_211,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_347])).

tff(c_356,plain,
    ( ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_349])).

tff(c_367,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_356])).

tff(c_369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_367])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.42  
% 2.82/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.43  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.82/1.43  
% 2.82/1.43  %Foreground sorts:
% 2.82/1.43  
% 2.82/1.43  
% 2.82/1.43  %Background operators:
% 2.82/1.43  
% 2.82/1.43  
% 2.82/1.43  %Foreground operators:
% 2.82/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.82/1.43  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.82/1.43  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.82/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.43  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.82/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.43  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.82/1.43  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.82/1.43  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.82/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.43  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.82/1.43  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.82/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.82/1.43  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.82/1.43  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.82/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.43  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.82/1.43  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.82/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.82/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.82/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.43  
% 2.82/1.45  tff(f_184, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_orders_1(C, k1_orders_1(u1_struct_0(A))) => (![D]: (m2_orders_2(D, A, C) => ((B = k1_funct_1(C, u1_struct_0(A))) => (k3_orders_2(A, D, B) = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_orders_2)).
% 2.82/1.45  tff(f_74, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.82/1.45  tff(f_54, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.82/1.45  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 2.82/1.45  tff(f_130, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 2.82/1.45  tff(f_159, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_orders_1(D, k1_orders_1(u1_struct_0(A))) => (![E]: (m2_orders_2(E, A, D) => ((r2_hidden(B, E) & (C = k1_funct_1(D, u1_struct_0(A)))) => r3_orders_2(A, C, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_orders_2)).
% 2.82/1.45  tff(f_89, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.82/1.45  tff(f_104, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_orders_2)).
% 2.82/1.45  tff(c_26, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.82/1.45  tff(c_30, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.82/1.45  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.82/1.45  tff(c_42, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.82/1.45  tff(c_40, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.82/1.45  tff(c_38, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.82/1.45  tff(c_36, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.82/1.45  tff(c_32, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.82/1.45  tff(c_89, plain, (![C_96, A_97, B_98]: (m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~m2_orders_2(C_96, A_97, B_98) | ~m1_orders_1(B_98, k1_orders_1(u1_struct_0(A_97))) | ~l1_orders_2(A_97) | ~v5_orders_2(A_97) | ~v4_orders_2(A_97) | ~v3_orders_2(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.82/1.45  tff(c_91, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_89])).
% 2.82/1.45  tff(c_94, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_32, c_91])).
% 2.82/1.45  tff(c_95, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_94])).
% 2.82/1.45  tff(c_34, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.82/1.45  tff(c_6, plain, (![A_4, B_5, C_6]: (m1_subset_1(k3_orders_2(A_4, B_5, C_6), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_subset_1(C_6, u1_struct_0(A_4)) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_orders_2(A_4) | ~v5_orders_2(A_4) | ~v4_orders_2(A_4) | ~v3_orders_2(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.82/1.45  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.82/1.45  tff(c_28, plain, (k1_funct_1('#skF_4', u1_struct_0('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.82/1.45  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.82/1.45  tff(c_101, plain, (![B_105, D_106, A_107, C_108]: (r2_hidden(B_105, D_106) | ~r2_hidden(B_105, k3_orders_2(A_107, D_106, C_108)) | ~m1_subset_1(D_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~m1_subset_1(C_108, u1_struct_0(A_107)) | ~m1_subset_1(B_105, u1_struct_0(A_107)) | ~l1_orders_2(A_107) | ~v5_orders_2(A_107) | ~v4_orders_2(A_107) | ~v3_orders_2(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.82/1.45  tff(c_188, plain, (![A_139, A_140, D_141, C_142]: (r2_hidden('#skF_1'(A_139, k3_orders_2(A_140, D_141, C_142)), D_141) | ~m1_subset_1(D_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~m1_subset_1(C_142, u1_struct_0(A_140)) | ~m1_subset_1('#skF_1'(A_139, k3_orders_2(A_140, D_141, C_142)), u1_struct_0(A_140)) | ~l1_orders_2(A_140) | ~v5_orders_2(A_140) | ~v4_orders_2(A_140) | ~v3_orders_2(A_140) | v2_struct_0(A_140) | k3_orders_2(A_140, D_141, C_142)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_140, D_141, C_142), k1_zfmisc_1(A_139)))), inference(resolution, [status(thm)], [c_2, c_101])).
% 2.82/1.45  tff(c_200, plain, (![A_145, D_146, C_147]: (r2_hidden('#skF_1'(u1_struct_0(A_145), k3_orders_2(A_145, D_146, C_147)), D_146) | ~m1_subset_1(D_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~m1_subset_1(C_147, u1_struct_0(A_145)) | ~l1_orders_2(A_145) | ~v5_orders_2(A_145) | ~v4_orders_2(A_145) | ~v3_orders_2(A_145) | v2_struct_0(A_145) | k3_orders_2(A_145, D_146, C_147)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_145, D_146, C_147), k1_zfmisc_1(u1_struct_0(A_145))))), inference(resolution, [status(thm)], [c_4, c_188])).
% 2.82/1.45  tff(c_24, plain, (![A_36, D_64, B_52, E_66]: (r3_orders_2(A_36, k1_funct_1(D_64, u1_struct_0(A_36)), B_52) | ~r2_hidden(B_52, E_66) | ~m2_orders_2(E_66, A_36, D_64) | ~m1_orders_1(D_64, k1_orders_1(u1_struct_0(A_36))) | ~m1_subset_1(k1_funct_1(D_64, u1_struct_0(A_36)), u1_struct_0(A_36)) | ~m1_subset_1(B_52, u1_struct_0(A_36)) | ~l1_orders_2(A_36) | ~v5_orders_2(A_36) | ~v4_orders_2(A_36) | ~v3_orders_2(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.82/1.45  tff(c_291, plain, (![A_190, D_193, A_192, D_194, C_191]: (r3_orders_2(A_190, k1_funct_1(D_193, u1_struct_0(A_190)), '#skF_1'(u1_struct_0(A_192), k3_orders_2(A_192, D_194, C_191))) | ~m2_orders_2(D_194, A_190, D_193) | ~m1_orders_1(D_193, k1_orders_1(u1_struct_0(A_190))) | ~m1_subset_1(k1_funct_1(D_193, u1_struct_0(A_190)), u1_struct_0(A_190)) | ~m1_subset_1('#skF_1'(u1_struct_0(A_192), k3_orders_2(A_192, D_194, C_191)), u1_struct_0(A_190)) | ~l1_orders_2(A_190) | ~v5_orders_2(A_190) | ~v4_orders_2(A_190) | ~v3_orders_2(A_190) | v2_struct_0(A_190) | ~m1_subset_1(D_194, k1_zfmisc_1(u1_struct_0(A_192))) | ~m1_subset_1(C_191, u1_struct_0(A_192)) | ~l1_orders_2(A_192) | ~v5_orders_2(A_192) | ~v4_orders_2(A_192) | ~v3_orders_2(A_192) | v2_struct_0(A_192) | k3_orders_2(A_192, D_194, C_191)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_192, D_194, C_191), k1_zfmisc_1(u1_struct_0(A_192))))), inference(resolution, [status(thm)], [c_200, c_24])).
% 2.82/1.45  tff(c_296, plain, (![A_192, D_194, C_191]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0(A_192), k3_orders_2(A_192, D_194, C_191))) | ~m2_orders_2(D_194, '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0(A_192), k3_orders_2(A_192, D_194, C_191)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(D_194, k1_zfmisc_1(u1_struct_0(A_192))) | ~m1_subset_1(C_191, u1_struct_0(A_192)) | ~l1_orders_2(A_192) | ~v5_orders_2(A_192) | ~v4_orders_2(A_192) | ~v3_orders_2(A_192) | v2_struct_0(A_192) | k3_orders_2(A_192, D_194, C_191)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_192, D_194, C_191), k1_zfmisc_1(u1_struct_0(A_192))))), inference(superposition, [status(thm), theory('equality')], [c_28, c_291])).
% 2.82/1.45  tff(c_299, plain, (![A_192, D_194, C_191]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0(A_192), k3_orders_2(A_192, D_194, C_191))) | ~m2_orders_2(D_194, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0(A_192), k3_orders_2(A_192, D_194, C_191)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(D_194, k1_zfmisc_1(u1_struct_0(A_192))) | ~m1_subset_1(C_191, u1_struct_0(A_192)) | ~l1_orders_2(A_192) | ~v5_orders_2(A_192) | ~v4_orders_2(A_192) | ~v3_orders_2(A_192) | v2_struct_0(A_192) | k3_orders_2(A_192, D_194, C_191)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_192, D_194, C_191), k1_zfmisc_1(u1_struct_0(A_192))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_28, c_32, c_296])).
% 2.82/1.45  tff(c_306, plain, (![A_200, D_201, C_202]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0(A_200), k3_orders_2(A_200, D_201, C_202))) | ~m2_orders_2(D_201, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0(A_200), k3_orders_2(A_200, D_201, C_202)), u1_struct_0('#skF_2')) | ~m1_subset_1(D_201, k1_zfmisc_1(u1_struct_0(A_200))) | ~m1_subset_1(C_202, u1_struct_0(A_200)) | ~l1_orders_2(A_200) | ~v5_orders_2(A_200) | ~v4_orders_2(A_200) | ~v3_orders_2(A_200) | v2_struct_0(A_200) | k3_orders_2(A_200, D_201, C_202)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_200, D_201, C_202), k1_zfmisc_1(u1_struct_0(A_200))))), inference(negUnitSimplification, [status(thm)], [c_44, c_299])).
% 2.82/1.45  tff(c_310, plain, (![D_201, C_202]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_201, C_202))) | ~m2_orders_2(D_201, '#skF_2', '#skF_4') | ~m1_subset_1(D_201, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_202, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_201, C_202)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_201, C_202), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_306])).
% 2.82/1.45  tff(c_313, plain, (![D_201, C_202]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_201, C_202))) | ~m2_orders_2(D_201, '#skF_2', '#skF_4') | ~m1_subset_1(D_201, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_202, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_201, C_202)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_201, C_202), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_310])).
% 2.82/1.45  tff(c_315, plain, (![D_203, C_204]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_203, C_204))) | ~m2_orders_2(D_203, '#skF_2', '#skF_4') | ~m1_subset_1(D_203, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_204, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_203, C_204)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_203, C_204), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_313])).
% 2.82/1.45  tff(c_14, plain, (![A_11, B_12, C_13]: (r1_orders_2(A_11, B_12, C_13) | ~r3_orders_2(A_11, B_12, C_13) | ~m1_subset_1(C_13, u1_struct_0(A_11)) | ~m1_subset_1(B_12, u1_struct_0(A_11)) | ~l1_orders_2(A_11) | ~v3_orders_2(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.82/1.45  tff(c_317, plain, (![D_203, C_204]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_203, C_204))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_203, C_204)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(D_203, '#skF_2', '#skF_4') | ~m1_subset_1(D_203, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_204, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_203, C_204)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_203, C_204), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_315, c_14])).
% 2.82/1.45  tff(c_320, plain, (![D_203, C_204]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_203, C_204))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_203, C_204)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m2_orders_2(D_203, '#skF_2', '#skF_4') | ~m1_subset_1(D_203, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_204, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_203, C_204)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_203, C_204), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_34, c_317])).
% 2.82/1.45  tff(c_322, plain, (![D_205, C_206]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_205, C_206))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_205, C_206)), u1_struct_0('#skF_2')) | ~m2_orders_2(D_205, '#skF_2', '#skF_4') | ~m1_subset_1(D_205, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_206, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_205, C_206)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_205, C_206), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_320])).
% 2.82/1.45  tff(c_327, plain, (![D_207, C_208]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_207, C_208))) | ~m2_orders_2(D_207, '#skF_2', '#skF_4') | ~m1_subset_1(D_207, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_208, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_207, C_208)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_207, C_208), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_322])).
% 2.82/1.45  tff(c_106, plain, (![A_109, B_110, C_111, D_112]: (r2_orders_2(A_109, B_110, C_111) | ~r2_hidden(B_110, k3_orders_2(A_109, D_112, C_111)) | ~m1_subset_1(D_112, k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_subset_1(C_111, u1_struct_0(A_109)) | ~m1_subset_1(B_110, u1_struct_0(A_109)) | ~l1_orders_2(A_109) | ~v5_orders_2(A_109) | ~v4_orders_2(A_109) | ~v3_orders_2(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.82/1.45  tff(c_226, plain, (![A_158, A_159, D_160, C_161]: (r2_orders_2(A_158, '#skF_1'(A_159, k3_orders_2(A_158, D_160, C_161)), C_161) | ~m1_subset_1(D_160, k1_zfmisc_1(u1_struct_0(A_158))) | ~m1_subset_1(C_161, u1_struct_0(A_158)) | ~m1_subset_1('#skF_1'(A_159, k3_orders_2(A_158, D_160, C_161)), u1_struct_0(A_158)) | ~l1_orders_2(A_158) | ~v5_orders_2(A_158) | ~v4_orders_2(A_158) | ~v3_orders_2(A_158) | v2_struct_0(A_158) | k3_orders_2(A_158, D_160, C_161)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_158, D_160, C_161), k1_zfmisc_1(A_159)))), inference(resolution, [status(thm)], [c_2, c_106])).
% 2.82/1.45  tff(c_231, plain, (![A_162, D_163, C_164]: (r2_orders_2(A_162, '#skF_1'(u1_struct_0(A_162), k3_orders_2(A_162, D_163, C_164)), C_164) | ~m1_subset_1(D_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~m1_subset_1(C_164, u1_struct_0(A_162)) | ~l1_orders_2(A_162) | ~v5_orders_2(A_162) | ~v4_orders_2(A_162) | ~v3_orders_2(A_162) | v2_struct_0(A_162) | k3_orders_2(A_162, D_163, C_164)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_162, D_163, C_164), k1_zfmisc_1(u1_struct_0(A_162))))), inference(resolution, [status(thm)], [c_4, c_226])).
% 2.82/1.45  tff(c_16, plain, (![A_14, C_20, B_18]: (~r2_orders_2(A_14, C_20, B_18) | ~r1_orders_2(A_14, B_18, C_20) | ~m1_subset_1(C_20, u1_struct_0(A_14)) | ~m1_subset_1(B_18, u1_struct_0(A_14)) | ~l1_orders_2(A_14) | ~v5_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.82/1.45  tff(c_234, plain, (![A_162, C_164, D_163]: (~r1_orders_2(A_162, C_164, '#skF_1'(u1_struct_0(A_162), k3_orders_2(A_162, D_163, C_164))) | ~m1_subset_1('#skF_1'(u1_struct_0(A_162), k3_orders_2(A_162, D_163, C_164)), u1_struct_0(A_162)) | ~m1_subset_1(D_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~m1_subset_1(C_164, u1_struct_0(A_162)) | ~l1_orders_2(A_162) | ~v5_orders_2(A_162) | ~v4_orders_2(A_162) | ~v3_orders_2(A_162) | v2_struct_0(A_162) | k3_orders_2(A_162, D_163, C_164)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_162, D_163, C_164), k1_zfmisc_1(u1_struct_0(A_162))))), inference(resolution, [status(thm)], [c_231, c_16])).
% 2.82/1.45  tff(c_330, plain, (![D_207]: (~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_207, '#skF_3')), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(D_207, '#skF_2', '#skF_4') | ~m1_subset_1(D_207, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_207, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_207, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_327, c_234])).
% 2.82/1.45  tff(c_333, plain, (![D_207]: (~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_207, '#skF_3')), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m2_orders_2(D_207, '#skF_2', '#skF_4') | ~m1_subset_1(D_207, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', D_207, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_207, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42, c_40, c_38, c_36, c_330])).
% 2.82/1.45  tff(c_335, plain, (![D_209]: (~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_209, '#skF_3')), u1_struct_0('#skF_2')) | ~m2_orders_2(D_209, '#skF_2', '#skF_4') | ~m1_subset_1(D_209, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', D_209, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_209, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_333])).
% 2.82/1.45  tff(c_340, plain, (![D_210]: (~m2_orders_2(D_210, '#skF_2', '#skF_4') | ~m1_subset_1(D_210, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', D_210, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_210, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_335])).
% 2.82/1.45  tff(c_344, plain, (![B_5]: (~m2_orders_2(B_5, '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_5, '#skF_3')=k1_xboole_0 | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_340])).
% 2.82/1.45  tff(c_347, plain, (![B_5]: (~m2_orders_2(B_5, '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_5, '#skF_3')=k1_xboole_0 | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_344])).
% 2.82/1.45  tff(c_349, plain, (![B_211]: (~m2_orders_2(B_211, '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_211, '#skF_3')=k1_xboole_0 | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_347])).
% 2.82/1.45  tff(c_356, plain, (~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_349])).
% 2.82/1.45  tff(c_367, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_356])).
% 2.82/1.45  tff(c_369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_367])).
% 2.82/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.45  
% 2.82/1.45  Inference rules
% 2.82/1.45  ----------------------
% 2.82/1.45  #Ref     : 0
% 2.82/1.45  #Sup     : 58
% 2.82/1.45  #Fact    : 0
% 2.82/1.45  #Define  : 0
% 2.82/1.45  #Split   : 1
% 2.82/1.45  #Chain   : 0
% 2.82/1.45  #Close   : 0
% 2.82/1.45  
% 2.82/1.45  Ordering : KBO
% 2.82/1.45  
% 2.82/1.45  Simplification rules
% 2.82/1.45  ----------------------
% 2.82/1.45  #Subsume      : 8
% 2.82/1.45  #Demod        : 99
% 2.82/1.45  #Tautology    : 10
% 2.82/1.45  #SimpNegUnit  : 22
% 2.82/1.45  #BackRed      : 0
% 2.82/1.45  
% 2.82/1.45  #Partial instantiations: 0
% 2.82/1.45  #Strategies tried      : 1
% 2.82/1.45  
% 2.82/1.45  Timing (in seconds)
% 2.82/1.45  ----------------------
% 2.82/1.45  Preprocessing        : 0.33
% 2.82/1.45  Parsing              : 0.19
% 2.82/1.45  CNF conversion       : 0.03
% 2.82/1.45  Main loop            : 0.34
% 2.82/1.45  Inferencing          : 0.15
% 2.82/1.45  Reduction            : 0.09
% 2.82/1.45  Demodulation         : 0.06
% 2.82/1.45  BG Simplification    : 0.02
% 2.82/1.45  Subsumption          : 0.07
% 2.82/1.45  Abstraction          : 0.01
% 2.82/1.45  MUC search           : 0.00
% 2.82/1.45  Cooper               : 0.00
% 2.82/1.45  Total                : 0.71
% 2.82/1.45  Index Insertion      : 0.00
% 2.82/1.45  Index Deletion       : 0.00
% 2.82/1.45  Index Matching       : 0.00
% 2.82/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
