%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:53 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 330 expanded)
%              Number of leaves         :   37 ( 149 expanded)
%              Depth                    :   30
%              Number of atoms          :  365 (1713 expanded)
%              Number of equality atoms :   36 ( 235 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_188,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_orders_2)).

tff(f_78,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_41,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_58,axiom,(
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

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_134,axiom,(
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

tff(f_163,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_orders_2)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_108,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r1_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

tff(c_28,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_44,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_42,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_40,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_38,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_34,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_32,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_76,plain,(
    ! [C_98,A_99,B_100] :
      ( m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m2_orders_2(C_98,A_99,B_100)
      | ~ m1_orders_1(B_100,k1_orders_1(u1_struct_0(A_99)))
      | ~ l1_orders_2(A_99)
      | ~ v5_orders_2(A_99)
      | ~ v4_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_78,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_76])).

tff(c_81,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_34,c_78])).

tff(c_82,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_81])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_6,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_104,plain,(
    ! [A_103,B_104,C_105] :
      ( m1_subset_1(k3_orders_2(A_103,B_104,C_105),k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(C_105,u1_struct_0(A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [A_115,A_116,B_117,C_118] :
      ( m1_subset_1(A_115,u1_struct_0(A_116))
      | ~ r2_hidden(A_115,k3_orders_2(A_116,B_117,C_118))
      | ~ m1_subset_1(C_118,u1_struct_0(A_116))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_orders_2(A_116)
      | ~ v5_orders_2(A_116)
      | ~ v4_orders_2(A_116)
      | ~ v3_orders_2(A_116)
      | v2_struct_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_104,c_2])).

tff(c_138,plain,(
    ! [A_116,B_117,C_118] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_116,B_117,C_118)),u1_struct_0(A_116))
      | ~ m1_subset_1(C_118,u1_struct_0(A_116))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_orders_2(A_116)
      | ~ v5_orders_2(A_116)
      | ~ v4_orders_2(A_116)
      | ~ v3_orders_2(A_116)
      | v2_struct_0(A_116)
      | k3_orders_2(A_116,B_117,C_118) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_30,plain,(
    k1_funct_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_129,plain,(
    ! [B_111,D_112,A_113,C_114] :
      ( r2_hidden(B_111,D_112)
      | ~ r2_hidden(B_111,k3_orders_2(A_113,D_112,C_114))
      | ~ m1_subset_1(D_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_subset_1(C_114,u1_struct_0(A_113))
      | ~ m1_subset_1(B_111,u1_struct_0(A_113))
      | ~ l1_orders_2(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v4_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_206,plain,(
    ! [A_137,D_138,C_139] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_137,D_138,C_139)),D_138)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ m1_subset_1(C_139,u1_struct_0(A_137))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_137,D_138,C_139)),u1_struct_0(A_137))
      | ~ l1_orders_2(A_137)
      | ~ v5_orders_2(A_137)
      | ~ v4_orders_2(A_137)
      | ~ v3_orders_2(A_137)
      | v2_struct_0(A_137)
      | k3_orders_2(A_137,D_138,C_139) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_129])).

tff(c_225,plain,(
    ! [A_146,B_147,C_148] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_146,B_147,C_148)),B_147)
      | ~ m1_subset_1(C_148,u1_struct_0(A_146))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_orders_2(A_146)
      | ~ v5_orders_2(A_146)
      | ~ v4_orders_2(A_146)
      | ~ v3_orders_2(A_146)
      | v2_struct_0(A_146)
      | k3_orders_2(A_146,B_147,C_148) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_138,c_206])).

tff(c_85,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_1,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_211,plain,(
    ! [D_138,C_139] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_138,C_139)),D_138)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_138,C_139) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_138,C_139)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_85,c_206])).

tff(c_215,plain,(
    ! [D_138,C_139] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_138,C_139)),D_138)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_138,C_139) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_138,C_139)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_211])).

tff(c_216,plain,(
    ! [D_138,C_139] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_138,C_139)),D_138)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_138,C_139) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_138,C_139)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_215])).

tff(c_230,plain,(
    ! [C_148] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_148)),'#skF_5')
      | ~ m1_subset_1(C_148,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_148) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_225,c_216])).

tff(c_243,plain,(
    ! [C_148] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_148)),'#skF_5')
      | ~ m1_subset_1(C_148,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_148) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_82,c_230])).

tff(c_248,plain,(
    ! [C_149] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_149)),'#skF_5')
      | ~ m1_subset_1(C_149,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_149) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_243])).

tff(c_26,plain,(
    ! [A_38,D_66,B_54,E_68] :
      ( r3_orders_2(A_38,k1_funct_1(D_66,u1_struct_0(A_38)),B_54)
      | ~ r2_hidden(B_54,E_68)
      | ~ m2_orders_2(E_68,A_38,D_66)
      | ~ m1_orders_1(D_66,k1_orders_1(u1_struct_0(A_38)))
      | ~ m1_subset_1(k1_funct_1(D_66,u1_struct_0(A_38)),u1_struct_0(A_38))
      | ~ m1_subset_1(B_54,u1_struct_0(A_38))
      | ~ l1_orders_2(A_38)
      | ~ v5_orders_2(A_38)
      | ~ v4_orders_2(A_38)
      | ~ v3_orders_2(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_477,plain,(
    ! [A_195,D_196,C_197] :
      ( r3_orders_2(A_195,k1_funct_1(D_196,u1_struct_0(A_195)),'#skF_1'(k3_orders_2('#skF_2','#skF_5',C_197)))
      | ~ m2_orders_2('#skF_5',A_195,D_196)
      | ~ m1_orders_1(D_196,k1_orders_1(u1_struct_0(A_195)))
      | ~ m1_subset_1(k1_funct_1(D_196,u1_struct_0(A_195)),u1_struct_0(A_195))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_197)),u1_struct_0(A_195))
      | ~ l1_orders_2(A_195)
      | ~ v5_orders_2(A_195)
      | ~ v4_orders_2(A_195)
      | ~ v3_orders_2(A_195)
      | v2_struct_0(A_195)
      | ~ m1_subset_1(C_197,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_197) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_248,c_26])).

tff(c_482,plain,(
    ! [C_197] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_197)))
      | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_197)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_197,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_197) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_477])).

tff(c_485,plain,(
    ! [C_197] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_197)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_197)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_197,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_197) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_30,c_34,c_32,c_482])).

tff(c_487,plain,(
    ! [C_198] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_198)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_198)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_198,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_198) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_485])).

tff(c_491,plain,(
    ! [C_118] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_118)))
      | ~ m1_subset_1(C_118,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_118) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_138,c_487])).

tff(c_497,plain,(
    ! [C_118] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_118)))
      | ~ m1_subset_1(C_118,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_118) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_82,c_491])).

tff(c_500,plain,(
    ! [C_199] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_199)))
      | ~ m1_subset_1(C_199,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_199) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_497])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_orders_2(A_13,B_14,C_15)
      | ~ r3_orders_2(A_13,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_13))
      | ~ m1_subset_1(B_14,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13)
      | ~ v3_orders_2(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_502,plain,(
    ! [C_199] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_199)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_199)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_199,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_199) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_500,c_16])).

tff(c_505,plain,(
    ! [C_199] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_199)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_199)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_199,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_199) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_36,c_502])).

tff(c_507,plain,(
    ! [C_200] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_200)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_200)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_200,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_200) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_505])).

tff(c_511,plain,(
    ! [C_118] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_118)))
      | ~ m1_subset_1(C_118,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_118) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_138,c_507])).

tff(c_517,plain,(
    ! [C_118] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_118)))
      | ~ m1_subset_1(C_118,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_118) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_82,c_511])).

tff(c_520,plain,(
    ! [C_201] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_201)))
      | ~ m1_subset_1(C_201,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_201) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_517])).

tff(c_165,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( r2_orders_2(A_124,B_125,C_126)
      | ~ r2_hidden(B_125,k3_orders_2(A_124,D_127,C_126))
      | ~ m1_subset_1(D_127,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ m1_subset_1(C_126,u1_struct_0(A_124))
      | ~ m1_subset_1(B_125,u1_struct_0(A_124))
      | ~ l1_orders_2(A_124)
      | ~ v5_orders_2(A_124)
      | ~ v4_orders_2(A_124)
      | ~ v3_orders_2(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_257,plain,(
    ! [A_150,D_151,C_152] :
      ( r2_orders_2(A_150,'#skF_1'(k3_orders_2(A_150,D_151,C_152)),C_152)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ m1_subset_1(C_152,u1_struct_0(A_150))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_150,D_151,C_152)),u1_struct_0(A_150))
      | ~ l1_orders_2(A_150)
      | ~ v5_orders_2(A_150)
      | ~ v4_orders_2(A_150)
      | ~ v3_orders_2(A_150)
      | v2_struct_0(A_150)
      | k3_orders_2(A_150,D_151,C_152) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_165])).

tff(c_274,plain,(
    ! [A_155,B_156,C_157] :
      ( r2_orders_2(A_155,'#skF_1'(k3_orders_2(A_155,B_156,C_157)),C_157)
      | ~ m1_subset_1(C_157,u1_struct_0(A_155))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_orders_2(A_155)
      | ~ v5_orders_2(A_155)
      | ~ v4_orders_2(A_155)
      | ~ v3_orders_2(A_155)
      | v2_struct_0(A_155)
      | k3_orders_2(A_155,B_156,C_157) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_138,c_257])).

tff(c_18,plain,(
    ! [A_16,C_22,B_20] :
      ( ~ r2_orders_2(A_16,C_22,B_20)
      | ~ r1_orders_2(A_16,B_20,C_22)
      | ~ m1_subset_1(C_22,u1_struct_0(A_16))
      | ~ m1_subset_1(B_20,u1_struct_0(A_16))
      | ~ l1_orders_2(A_16)
      | ~ v5_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_277,plain,(
    ! [A_155,C_157,B_156] :
      ( ~ r1_orders_2(A_155,C_157,'#skF_1'(k3_orders_2(A_155,B_156,C_157)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_155,B_156,C_157)),u1_struct_0(A_155))
      | ~ m1_subset_1(C_157,u1_struct_0(A_155))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_orders_2(A_155)
      | ~ v5_orders_2(A_155)
      | ~ v4_orders_2(A_155)
      | ~ v3_orders_2(A_155)
      | v2_struct_0(A_155)
      | k3_orders_2(A_155,B_156,C_157) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_274,c_18])).

tff(c_523,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_520,c_277])).

tff(c_529,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_44,c_42,c_40,c_38,c_82,c_523])).

tff(c_530,plain,(
    ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_46,c_529])).

tff(c_537,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_138,c_530])).

tff(c_543,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_82,c_36,c_537])).

tff(c_545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_46,c_543])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:16:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.48  
% 3.14/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.48  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.14/1.48  
% 3.14/1.48  %Foreground sorts:
% 3.14/1.48  
% 3.14/1.48  
% 3.14/1.48  %Background operators:
% 3.14/1.48  
% 3.14/1.48  
% 3.14/1.48  %Foreground operators:
% 3.14/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.14/1.48  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.14/1.48  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.14/1.48  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.14/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.48  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.14/1.48  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.14/1.48  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.14/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.14/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.14/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.48  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.14/1.48  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.14/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.14/1.48  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.14/1.48  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.48  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.14/1.48  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.14/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.48  
% 3.27/1.50  tff(f_188, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_orders_1(C, k1_orders_1(u1_struct_0(A))) => (![D]: (m2_orders_2(D, A, C) => ((B = k1_funct_1(C, u1_struct_0(A))) => (k3_orders_2(A, D, B) = k1_xboole_0)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_orders_2)).
% 3.27/1.50  tff(f_78, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.27/1.50  tff(f_41, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.27/1.50  tff(f_58, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 3.27/1.50  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.27/1.50  tff(f_134, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 3.27/1.50  tff(f_163, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_orders_1(D, k1_orders_1(u1_struct_0(A))) => (![E]: (m2_orders_2(E, A, D) => ((r2_hidden(B, E) & (C = k1_funct_1(D, u1_struct_0(A)))) => r3_orders_2(A, C, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_orders_2)).
% 3.27/1.50  tff(f_93, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.27/1.50  tff(f_108, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_orders_2)).
% 3.27/1.50  tff(c_28, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.27/1.50  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.27/1.50  tff(c_44, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.27/1.50  tff(c_42, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.27/1.50  tff(c_40, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.27/1.50  tff(c_38, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.27/1.50  tff(c_34, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.27/1.50  tff(c_32, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.27/1.50  tff(c_76, plain, (![C_98, A_99, B_100]: (m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~m2_orders_2(C_98, A_99, B_100) | ~m1_orders_1(B_100, k1_orders_1(u1_struct_0(A_99))) | ~l1_orders_2(A_99) | ~v5_orders_2(A_99) | ~v4_orders_2(A_99) | ~v3_orders_2(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.27/1.50  tff(c_78, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_76])).
% 3.27/1.50  tff(c_81, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_34, c_78])).
% 3.27/1.50  tff(c_82, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_81])).
% 3.27/1.50  tff(c_36, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.27/1.50  tff(c_6, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.50  tff(c_104, plain, (![A_103, B_104, C_105]: (m1_subset_1(k3_orders_2(A_103, B_104, C_105), k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(C_105, u1_struct_0(A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.27/1.50  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.50  tff(c_134, plain, (![A_115, A_116, B_117, C_118]: (m1_subset_1(A_115, u1_struct_0(A_116)) | ~r2_hidden(A_115, k3_orders_2(A_116, B_117, C_118)) | ~m1_subset_1(C_118, u1_struct_0(A_116)) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_orders_2(A_116) | ~v5_orders_2(A_116) | ~v4_orders_2(A_116) | ~v3_orders_2(A_116) | v2_struct_0(A_116))), inference(resolution, [status(thm)], [c_104, c_2])).
% 3.27/1.50  tff(c_138, plain, (![A_116, B_117, C_118]: (m1_subset_1('#skF_1'(k3_orders_2(A_116, B_117, C_118)), u1_struct_0(A_116)) | ~m1_subset_1(C_118, u1_struct_0(A_116)) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_orders_2(A_116) | ~v5_orders_2(A_116) | ~v4_orders_2(A_116) | ~v3_orders_2(A_116) | v2_struct_0(A_116) | k3_orders_2(A_116, B_117, C_118)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_134])).
% 3.27/1.50  tff(c_30, plain, (k1_funct_1('#skF_4', u1_struct_0('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.27/1.50  tff(c_129, plain, (![B_111, D_112, A_113, C_114]: (r2_hidden(B_111, D_112) | ~r2_hidden(B_111, k3_orders_2(A_113, D_112, C_114)) | ~m1_subset_1(D_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~m1_subset_1(C_114, u1_struct_0(A_113)) | ~m1_subset_1(B_111, u1_struct_0(A_113)) | ~l1_orders_2(A_113) | ~v5_orders_2(A_113) | ~v4_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.27/1.50  tff(c_206, plain, (![A_137, D_138, C_139]: (r2_hidden('#skF_1'(k3_orders_2(A_137, D_138, C_139)), D_138) | ~m1_subset_1(D_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~m1_subset_1(C_139, u1_struct_0(A_137)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_137, D_138, C_139)), u1_struct_0(A_137)) | ~l1_orders_2(A_137) | ~v5_orders_2(A_137) | ~v4_orders_2(A_137) | ~v3_orders_2(A_137) | v2_struct_0(A_137) | k3_orders_2(A_137, D_138, C_139)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_129])).
% 3.27/1.50  tff(c_225, plain, (![A_146, B_147, C_148]: (r2_hidden('#skF_1'(k3_orders_2(A_146, B_147, C_148)), B_147) | ~m1_subset_1(C_148, u1_struct_0(A_146)) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_orders_2(A_146) | ~v5_orders_2(A_146) | ~v4_orders_2(A_146) | ~v3_orders_2(A_146) | v2_struct_0(A_146) | k3_orders_2(A_146, B_147, C_148)=k1_xboole_0)), inference(resolution, [status(thm)], [c_138, c_206])).
% 3.27/1.50  tff(c_85, plain, (![A_1]: (m1_subset_1(A_1, u1_struct_0('#skF_2')) | ~r2_hidden(A_1, '#skF_5'))), inference(resolution, [status(thm)], [c_82, c_2])).
% 3.27/1.50  tff(c_211, plain, (![D_138, C_139]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_138, C_139)), D_138) | ~m1_subset_1(D_138, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_139, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_138, C_139)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_138, C_139)), '#skF_5'))), inference(resolution, [status(thm)], [c_85, c_206])).
% 3.27/1.50  tff(c_215, plain, (![D_138, C_139]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_138, C_139)), D_138) | ~m1_subset_1(D_138, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_139, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_138, C_139)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_138, C_139)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_211])).
% 3.27/1.50  tff(c_216, plain, (![D_138, C_139]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_138, C_139)), D_138) | ~m1_subset_1(D_138, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_139, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_138, C_139)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_138, C_139)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_46, c_215])).
% 3.27/1.50  tff(c_230, plain, (![C_148]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_148)), '#skF_5') | ~m1_subset_1(C_148, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_148)=k1_xboole_0)), inference(resolution, [status(thm)], [c_225, c_216])).
% 3.27/1.50  tff(c_243, plain, (![C_148]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_148)), '#skF_5') | ~m1_subset_1(C_148, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_148)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_82, c_230])).
% 3.27/1.50  tff(c_248, plain, (![C_149]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_149)), '#skF_5') | ~m1_subset_1(C_149, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_149)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_243])).
% 3.27/1.50  tff(c_26, plain, (![A_38, D_66, B_54, E_68]: (r3_orders_2(A_38, k1_funct_1(D_66, u1_struct_0(A_38)), B_54) | ~r2_hidden(B_54, E_68) | ~m2_orders_2(E_68, A_38, D_66) | ~m1_orders_1(D_66, k1_orders_1(u1_struct_0(A_38))) | ~m1_subset_1(k1_funct_1(D_66, u1_struct_0(A_38)), u1_struct_0(A_38)) | ~m1_subset_1(B_54, u1_struct_0(A_38)) | ~l1_orders_2(A_38) | ~v5_orders_2(A_38) | ~v4_orders_2(A_38) | ~v3_orders_2(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.27/1.50  tff(c_477, plain, (![A_195, D_196, C_197]: (r3_orders_2(A_195, k1_funct_1(D_196, u1_struct_0(A_195)), '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_197))) | ~m2_orders_2('#skF_5', A_195, D_196) | ~m1_orders_1(D_196, k1_orders_1(u1_struct_0(A_195))) | ~m1_subset_1(k1_funct_1(D_196, u1_struct_0(A_195)), u1_struct_0(A_195)) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_197)), u1_struct_0(A_195)) | ~l1_orders_2(A_195) | ~v5_orders_2(A_195) | ~v4_orders_2(A_195) | ~v3_orders_2(A_195) | v2_struct_0(A_195) | ~m1_subset_1(C_197, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_197)=k1_xboole_0)), inference(resolution, [status(thm)], [c_248, c_26])).
% 3.27/1.50  tff(c_482, plain, (![C_197]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_197))) | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_197)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_197, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_197)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_477])).
% 3.27/1.50  tff(c_485, plain, (![C_197]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_197))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_197)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_197, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_197)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_30, c_34, c_32, c_482])).
% 3.27/1.50  tff(c_487, plain, (![C_198]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_198))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_198)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_198, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_198)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_485])).
% 3.27/1.50  tff(c_491, plain, (![C_118]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_118))) | ~m1_subset_1(C_118, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_118)=k1_xboole_0)), inference(resolution, [status(thm)], [c_138, c_487])).
% 3.27/1.50  tff(c_497, plain, (![C_118]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_118))) | ~m1_subset_1(C_118, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_118)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_82, c_491])).
% 3.27/1.50  tff(c_500, plain, (![C_199]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_199))) | ~m1_subset_1(C_199, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_199)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_497])).
% 3.27/1.50  tff(c_16, plain, (![A_13, B_14, C_15]: (r1_orders_2(A_13, B_14, C_15) | ~r3_orders_2(A_13, B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_13)) | ~m1_subset_1(B_14, u1_struct_0(A_13)) | ~l1_orders_2(A_13) | ~v3_orders_2(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.27/1.50  tff(c_502, plain, (![C_199]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_199))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_199)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_199, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_199)=k1_xboole_0)), inference(resolution, [status(thm)], [c_500, c_16])).
% 3.27/1.50  tff(c_505, plain, (![C_199]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_199))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_199)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_199, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_199)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_36, c_502])).
% 3.27/1.50  tff(c_507, plain, (![C_200]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_200))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_200)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_200, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_200)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_505])).
% 3.27/1.50  tff(c_511, plain, (![C_118]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_118))) | ~m1_subset_1(C_118, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_118)=k1_xboole_0)), inference(resolution, [status(thm)], [c_138, c_507])).
% 3.27/1.50  tff(c_517, plain, (![C_118]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_118))) | ~m1_subset_1(C_118, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_118)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_82, c_511])).
% 3.27/1.50  tff(c_520, plain, (![C_201]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_201))) | ~m1_subset_1(C_201, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_201)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_517])).
% 3.27/1.50  tff(c_165, plain, (![A_124, B_125, C_126, D_127]: (r2_orders_2(A_124, B_125, C_126) | ~r2_hidden(B_125, k3_orders_2(A_124, D_127, C_126)) | ~m1_subset_1(D_127, k1_zfmisc_1(u1_struct_0(A_124))) | ~m1_subset_1(C_126, u1_struct_0(A_124)) | ~m1_subset_1(B_125, u1_struct_0(A_124)) | ~l1_orders_2(A_124) | ~v5_orders_2(A_124) | ~v4_orders_2(A_124) | ~v3_orders_2(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.27/1.50  tff(c_257, plain, (![A_150, D_151, C_152]: (r2_orders_2(A_150, '#skF_1'(k3_orders_2(A_150, D_151, C_152)), C_152) | ~m1_subset_1(D_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~m1_subset_1(C_152, u1_struct_0(A_150)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_150, D_151, C_152)), u1_struct_0(A_150)) | ~l1_orders_2(A_150) | ~v5_orders_2(A_150) | ~v4_orders_2(A_150) | ~v3_orders_2(A_150) | v2_struct_0(A_150) | k3_orders_2(A_150, D_151, C_152)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_165])).
% 3.27/1.50  tff(c_274, plain, (![A_155, B_156, C_157]: (r2_orders_2(A_155, '#skF_1'(k3_orders_2(A_155, B_156, C_157)), C_157) | ~m1_subset_1(C_157, u1_struct_0(A_155)) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_orders_2(A_155) | ~v5_orders_2(A_155) | ~v4_orders_2(A_155) | ~v3_orders_2(A_155) | v2_struct_0(A_155) | k3_orders_2(A_155, B_156, C_157)=k1_xboole_0)), inference(resolution, [status(thm)], [c_138, c_257])).
% 3.27/1.50  tff(c_18, plain, (![A_16, C_22, B_20]: (~r2_orders_2(A_16, C_22, B_20) | ~r1_orders_2(A_16, B_20, C_22) | ~m1_subset_1(C_22, u1_struct_0(A_16)) | ~m1_subset_1(B_20, u1_struct_0(A_16)) | ~l1_orders_2(A_16) | ~v5_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.27/1.50  tff(c_277, plain, (![A_155, C_157, B_156]: (~r1_orders_2(A_155, C_157, '#skF_1'(k3_orders_2(A_155, B_156, C_157))) | ~m1_subset_1('#skF_1'(k3_orders_2(A_155, B_156, C_157)), u1_struct_0(A_155)) | ~m1_subset_1(C_157, u1_struct_0(A_155)) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_orders_2(A_155) | ~v5_orders_2(A_155) | ~v4_orders_2(A_155) | ~v3_orders_2(A_155) | v2_struct_0(A_155) | k3_orders_2(A_155, B_156, C_157)=k1_xboole_0)), inference(resolution, [status(thm)], [c_274, c_18])).
% 3.27/1.50  tff(c_523, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_520, c_277])).
% 3.27/1.50  tff(c_529, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_44, c_42, c_40, c_38, c_82, c_523])).
% 3.27/1.50  tff(c_530, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_28, c_46, c_529])).
% 3.27/1.50  tff(c_537, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_138, c_530])).
% 3.27/1.50  tff(c_543, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_82, c_36, c_537])).
% 3.27/1.50  tff(c_545, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_46, c_543])).
% 3.27/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.50  
% 3.27/1.50  Inference rules
% 3.27/1.50  ----------------------
% 3.27/1.50  #Ref     : 0
% 3.27/1.50  #Sup     : 86
% 3.27/1.50  #Fact    : 0
% 3.27/1.50  #Define  : 0
% 3.27/1.50  #Split   : 1
% 3.27/1.50  #Chain   : 0
% 3.27/1.50  #Close   : 0
% 3.27/1.50  
% 3.27/1.50  Ordering : KBO
% 3.27/1.50  
% 3.27/1.50  Simplification rules
% 3.27/1.50  ----------------------
% 3.27/1.50  #Subsume      : 23
% 3.27/1.50  #Demod        : 179
% 3.27/1.50  #Tautology    : 12
% 3.27/1.50  #SimpNegUnit  : 42
% 3.27/1.50  #BackRed      : 0
% 3.27/1.50  
% 3.27/1.50  #Partial instantiations: 0
% 3.27/1.50  #Strategies tried      : 1
% 3.27/1.50  
% 3.27/1.50  Timing (in seconds)
% 3.27/1.50  ----------------------
% 3.27/1.51  Preprocessing        : 0.32
% 3.27/1.51  Parsing              : 0.17
% 3.27/1.51  CNF conversion       : 0.03
% 3.27/1.51  Main loop            : 0.36
% 3.27/1.51  Inferencing          : 0.15
% 3.27/1.51  Reduction            : 0.10
% 3.27/1.51  Demodulation         : 0.07
% 3.27/1.51  BG Simplification    : 0.02
% 3.27/1.51  Subsumption          : 0.07
% 3.27/1.51  Abstraction          : 0.02
% 3.27/1.51  MUC search           : 0.00
% 3.27/1.51  Cooper               : 0.00
% 3.27/1.51  Total                : 0.72
% 3.27/1.51  Index Insertion      : 0.00
% 3.27/1.51  Index Deletion       : 0.00
% 3.27/1.51  Index Matching       : 0.00
% 3.27/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
